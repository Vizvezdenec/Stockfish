/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (c) 2013 Ronald de Man
  Copyright (C) 2016 Marco Costalba, Lucas Braesch

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstring>   // For std::memset
#include <deque>
#include <fstream>
#include <iostream>
#include <list>
#include <sstream>
#include <type_traits>

#include "../bitboard.h"
#include "../movegen.h"
#include "../position.h"
#include "../search.h"
#include "../thread_win32.h"
#include "../types.h"

#include "tbprobe.h"

#ifndef _WIN32
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/stat.h>
#else
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#endif

using namespace Tablebases;

size_t Tablebases::MaxCardinality;

namespace {

// Each table has a set of flags: all of them refer to DTZ tables, the last one to WDL tables
enum TBFlag { STM = 1, Mapped = 2, WinPlies = 4, LossPlies = 8, SingleValue = 128 };

inline WDLScore operator-(WDLScore d) { return WDLScore(-int(d)); }
inline WDLScore operator+(WDLScore d1, WDLScore d2) { return WDLScore(int(d1) + int(d2)); }

inline Square operator^=(Square& s, int i) { return s = Square(int(s) ^ i); }
inline Square operator^(Square s, int i) { return Square(int(s) ^ i); }

// DTZ tables don't store valid scoers for moves that reset the rule50 counter
// like captures and pawn moves. Luckily we can easily recover the correct dtz
// if we know the position's WDL score.
int zeroing_move_dtz(WDLScore wdl)
{
    return wdl == WDLWin        ?  1   :
           wdl == WDLCursedWin  ?  101 :
           wdl == WDLCursedLoss ? -101 :
           wdl == WDLLoss       ? -1   : 0;
}

// Returns the sign of a number (-1, 0, 1)
template <typename T> int sign_of(T val) {
    return (T(0) < val) - (val < T(0));
}

// Numbers in Little Endian format used by sparseIndex[] to point into blockLength[]
struct SparseEntry {
    char block[4];   // Number of block
    char offset[2];  // Offset within the block
};

static_assert(sizeof(SparseEntry) == 6, "SparseEntry must be 6 bytes");

typedef uint16_t Sym; // Huffman symbol

struct LR {
    enum Side { Left, Right, Value };

    uint8_t lr[3]; // The first 12 bits is the left-hand symbol, the second 12
                   // bits is the right-hand symbol. If symbol has length 1,
                   // then the first byte is the stored value.
    template<Side S>
    Sym get() {
        return S == Left  ? ((lr[1] & 0xF) << 8) | lr[0] :
               S == Right ?  (lr[2] << 4) | (lr[1] >> 4) :
               S == Value ?   lr[0] : (assert(false), Sym(-1));
    }
};

static_assert(sizeof(LR) == 3, "LR tree entry must be 3 bytes");

const int TBPIECES = 6;

struct PairsData {
    int flags;
    size_t sizeofBlock;            // Block size in bytes
    size_t span;                   // About every span values there is a SparseIndex[] entry
    int blocksNum;                 // Number of blocks in the TB file
    int maxSymLen;                 // Maximum length in bits of the Huffman symbols
    int minSymLen;                 // Minimum length in bits of the Huffman symbols
    Sym* lowestSym;                // lowestSym[l] is the value of the lowest symbol of length l
    LR* btree;                     // btree[sym] stores the left and right symbols that expand sym
    uint16_t* blockLength;         // Number of stored positions (minus one) for each block: 1..65536
    int blockLengthSize;           // Size of blockLength[] table: padded so it's bigger than blocksNum
    SparseEntry* sparseIndex;      // Partial indices into blockLength[]
    size_t sparseIndexSize;        // Size of SparseIndex[] table
    uint8_t* data;                 // Start of Huffman compressed data
    std::vector<uint64_t> base64;  // Smallest symbol of length l padded to 64 bits is at base64[l - min_sym_len]
    std::vector<uint8_t> symlen;   // Number of values (-1) represented by a given Huffman symbol: 1..256
    Piece pieces[TBPIECES];        // Sequence of the pieces: order is critical to ensure the best compression
    uint64_t groupSize[TBPIECES];  // Size needed by a given subset of pieces: KRKN -> (KRK) + (N)
    uint8_t groupLen[TBPIECES];    // Number of pieces in a given group: KRKN -> (3) + (1)
};

// Helper struct to avoid to manually define WDLEntry copy c'tor as we should
// because default one is not compatible with std::atomic_bool.
struct Atomic {
    Atomic() = default;
    Atomic(const Atomic& e) { ready = e.ready.load(); } // MSVC 2013 wants assignment within body
    std::atomic_bool ready;
};

struct WDLEntry : public Atomic {
    WDLEntry(const Position& pos, Key keys[]);
   ~WDLEntry();

    void* baseAddress;
    uint64_t mapping;
    Key key;
    Key key2;
    int pieceCount;
    bool hasPawns;
    bool hasUniquePieces;
    union {
        struct {
            PairsData* precomp;
        } piece[2]; // One for each side to move

        struct {
            uint8_t pawnCount[2];
            struct {
                PairsData* precomp;
            } file[2][4];
        } pawn;
    };
};

struct DTZEntry {
    DTZEntry(const WDLEntry& wdl);
   ~DTZEntry();

    void* baseAddress;
    uint64_t mapping;
    Key key;
    Key key2;
    int pieceCount;
    bool hasPawns;
    bool hasUniquePieces;
    union {
        struct {
            PairsData* precomp;
            uint16_t map_idx[4]; // WDLWin, WDLLoss, WDLCursedWin, WDLCursedLoss
            uint8_t* map;
        } piece;

        struct {
            uint8_t pawnCount[2];
            struct {
                PairsData* precomp;
                uint16_t map_idx[4];
            } file[4];
            uint8_t* map;
        } pawn;
    };
};

typedef decltype(WDLEntry::piece) WDLPiece;
typedef decltype(DTZEntry::piece) DTZPiece;
typedef decltype(WDLEntry::pawn ) WDLPawn;
typedef decltype(DTZEntry::pawn ) DTZPawn;

auto item(WDLPiece& e, int stm, int  ) -> decltype(e[stm])& { return e[stm]; }
auto item(DTZPiece& e, int    , int  ) -> decltype(e)& { return e; }
auto item(WDLPawn&  e, int stm, int f) -> decltype(e.file[stm][f])& { return e.file[stm][f]; }
auto item(DTZPawn&  e, int    , int f) -> decltype(e.file[f])& { return e.file[f]; }

int MapPawns[SQUARE_NB];
int MapB1H1H7[SQUARE_NB];
int MapA1D1D4[SQUARE_NB];
int MapKK[10][SQUARE_NB]; // [MapA1D1D4][SQUARE_NB]

// Comparison function to sort leading pawns in ascending MapPawns[] order
bool pawns_comp(Square i, Square j) { return MapPawns[i] < MapPawns[j]; }
int off_A1H8(Square sq) { return int(rank_of(sq)) - file_of(sq); }

const uint8_t WDL_MAGIC[] = { 0x71, 0xE8, 0x23, 0x5D };
const uint8_t DTZ_MAGIC[] = { 0xD7, 0x66, 0x0C, 0xA5 };

const int wdl_to_dtz[] = { -1, -101, 0, 101, 1 };

const Value WDL_to_value[] = {
   -VALUE_MATE + MAX_PLY + 1,
    VALUE_DRAW - 2,
    VALUE_DRAW,
    VALUE_DRAW + 2,
    VALUE_MATE - MAX_PLY - 1
};

const std::string PieceToChar = " PNBRQK  pnbrqk";

Mutex TB_mutex;
std::string TBPaths;
std::deque<WDLEntry> WDLTable;
std::list<DTZEntry> DTZTable;

int Binomial[6][SQUARE_NB];    // [k][n] k elements from a set of n elements
int LeadPawnIdx[4][SQUARE_NB]; // [leadPawnsCnt - 1][SQUARE_NB]
int LeadPawnsGroupSize[4][4];  // [leadPawnsCnt - 1][FILE_A..FILE_D]

enum { BigEndian, LittleEndian };

template<typename T, int Half = sizeof(T) / 2, int End = sizeof(T) - 1>
inline void swap_byte(T& x)
{
    char tmp, *c = (char*)&x;
    if (Half) // Fix a MSVC 2015 warning
        for (int i = 0; i < Half; ++i)
            tmp = c[i], c[i] = c[End - i], c[End - i] = tmp;
}

template<typename T, int LE> T number(void* addr)
{
    const union { uint32_t i; char c[4]; } Le = { 0x01020304 };
    const bool IsLittleEndian = (Le.c[0] == 4);

    T v = *((T*)addr);
    if (LE != IsLittleEndian)
        swap_byte(v);
    return v;
}

class HashTable {

    typedef std::pair<Key, WDLEntry*> Entry;

    static const int TBHASHBITS = 10;
    static const int HSHMAX     = 5;

    Entry table[1 << TBHASHBITS][HSHMAX];

    void insert(Key key, WDLEntry* ptr) {
        Entry* entry = table[key >> (64 - TBHASHBITS)];

        for (int i = 0; i < HSHMAX; ++i, ++entry)
            if (!entry->second || entry->first == key) {
                *entry = std::make_pair(key, ptr);
                return;
            }

        std::cerr << "HSHMAX too low!" << std::endl;
        exit(1);
    }

public:
  WDLEntry* operator[](Key key) {
      Entry* entry = table[key >> (64 - TBHASHBITS)];

      for (int i = 0; i < HSHMAX; ++i, ++entry)
          if (entry->first == key)
              return entry->second;

      return nullptr;
  }

  void clear() { std::memset(table, 0, sizeof(table)); }
  void insert(const std::vector<PieceType>& pieces);
};

HashTable WDLHash;


class TBFile : public std::ifstream {

    std::string fname;

public:
    // Open the file with the given name found among the TBPaths directories
    // where the .rtbw and .rtbz files can be found. Multiple directories are
    // separated by ";" on Windows and by ":" on Unix-based operating systems.
    //
    // Example:
    // C:\tb\wdl345;C:\tb\wdl6;D:\tb\dtz345;D:\tb\dtz6
    TBFile(const std::string& f) {

#ifndef _WIN32
        const char SepChar = ':';
#else
        const char SepChar = ';';
#endif
        std::stringstream ss(TBPaths);
        std::string path;

        while (std::getline(ss, path, SepChar)) {
            fname = path + "/" + f;
            std::ifstream::open(fname);
            if (is_open())
                return;
        }
    }

    // Memory map the file and check it. File should be already open and
    // will be closed after mapping.
    uint8_t* map(void** baseAddress, uint64_t* mapping, const uint8_t TB_MAGIC[]) {

        if (!is_open()) {
            std::cerr << "Could not find " << fname << std::endl;
            *baseAddress = nullptr;
            return nullptr;
        }
        close();

#ifndef _WIN32
        struct stat statbuf;
        int fd = ::open(fname.c_str(), O_RDONLY);
        fstat(fd, &statbuf);
        *mapping = statbuf.st_size;
        *baseAddress = mmap(nullptr, statbuf.st_size, PROT_READ, MAP_SHARED, fd, 0);
        ::close(fd);

        if (*baseAddress == MAP_FAILED) {
            std::cerr << "Could not mmap() " << fname << std::endl;
            exit(1);
        }
#else
        HANDLE fd = CreateFile(fname.c_str(), GENERIC_READ, FILE_SHARE_READ, nullptr,
                               OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, nullptr);
        DWORD size_high;
        DWORD size_low = GetFileSize(fd, &size_high);
        HANDLE mmap = CreateFileMapping(fd, nullptr, PAGE_READONLY, size_high, size_low, nullptr);
        CloseHandle(fd);

        if (!mmap) {
            std::cerr << "CreateFileMapping() failed" << std::endl;
            exit(1);
        }

        *mapping = (uint64_t)mmap;
        *baseAddress = MapViewOfFile(mmap, FILE_MAP_READ, 0, 0, 0);

        if (!*baseAddress) {
            std::cerr << "MapViewOfFile() failed, name = " << fname
                      << ", error = " << GetLastError() << std::endl;
            exit(1);
        }
#endif
        uint8_t* data = (uint8_t*)*baseAddress;

        if (   *data++ != TB_MAGIC[0]
            || *data++ != TB_MAGIC[1]
            || *data++ != TB_MAGIC[2]
            || *data++ != TB_MAGIC[3]) {
            std::cerr << "Corrupted table in file " << fname << std::endl;
            unmap(*baseAddress, *mapping);
            *baseAddress = nullptr;
            return nullptr;
        }

        return data;
    }

    static void unmap(void* baseAddress, uint64_t mapping) {

#ifndef _WIN32
        munmap(baseAddress, mapping);
#else
        UnmapViewOfFile(baseAddress);
        CloseHandle((HANDLE)mapping);
#endif
    }
};

WDLEntry::WDLEntry(const Position& pos, Key keys[])
{
    memset(this, 0, sizeof(WDLEntry));

    ready = false;

    key = keys[WHITE];
    key2 = keys[BLACK];
    pieceCount = popcount(pos.pieces());
    hasPawns = pos.pieces(PAWN);

    for (Color c = WHITE; c <= BLACK; ++c)
        for (PieceType pt = PAWN; pt < KING; ++pt)
            if (popcount(pos.pieces(c, pt)) == 1)
                hasUniquePieces = true;

    if (hasPawns) {
        // Set the leading color. In case both sides have pawns the leading color
        // is the side with less pawns because this leads to better compression.
        bool c =   !pos.count<PAWN>(BLACK)
                || (   pos.count<PAWN>(WHITE)
                    && pos.count<PAWN>(BLACK) >= pos.count<PAWN>(WHITE));

        pawn.pawnCount[0] = pos.count<PAWN>(c ? WHITE : BLACK);
        pawn.pawnCount[1] = pos.count<PAWN>(c ? BLACK : WHITE);
    }
}

WDLEntry::~WDLEntry()
{
    if (baseAddress)
        TBFile::unmap(baseAddress, mapping);

    for (int i = 0; i < 2; ++i)
        if (hasPawns)
            for (File f = FILE_A; f <= FILE_D; ++f)
                delete pawn.file[i][f].precomp;
        else
            delete piece[i].precomp;
}

DTZEntry::DTZEntry(const WDLEntry& wdl)
{
    memset(this, 0, sizeof(DTZEntry));

    key = wdl.key;
    key2 = wdl.key2;
    pieceCount = wdl.pieceCount;
    hasPawns = wdl.hasPawns;
    hasUniquePieces = wdl.hasUniquePieces;

    if (hasPawns) {
        pawn.pawnCount[0] = wdl.pawn.pawnCount[0];
        pawn.pawnCount[1] = wdl.pawn.pawnCount[1];
    }
}

DTZEntry::~DTZEntry()
{
    if (baseAddress)
        TBFile::unmap(baseAddress, mapping);

    if (hasPawns)
        for (File f = FILE_A; f <= FILE_D; ++f)
            delete pawn.file[f].precomp;
    else
        delete piece.precomp;
}

// Given a position return a string of the form KQPvKRP, where KQP represents
// the white pieces if mirror == false and the black pieces if mirror == true.
std::string pos_code(const Position& pos, bool mirror = false)
{
    std::string w, b;

    for (PieceType pt = KING; pt >= PAWN; --pt) {
        w += std::string(popcount(pos.pieces(WHITE, pt)), PieceToChar[pt]);
        b += std::string(popcount(pos.pieces(BLACK, pt)), PieceToChar[pt]);
    }

    return mirror ? b + 'v' + w : w + 'v' + b;
}

void HashTable::insert(const std::vector<PieceType>& pieces)
{
    StateInfo st;
    Position pos;
    std::string code;

    for (PieceType pt : pieces)
        code += PieceToChar[pt];

    TBFile file(pos_code(pos.set(code, WHITE, &st)) + ".rtbw");

    if (!file.is_open())
        return;

    file.close();

    MaxCardinality = std::max(pieces.size(), MaxCardinality);

    Key keys[] = { pos.set(code, WHITE, &st).material_key(),
                   pos.set(code, BLACK, &st).material_key() };

    WDLTable.push_back(WDLEntry(pos.set(code, WHITE, &st), keys));

    insert(keys[WHITE], &WDLTable.back());
    insert(keys[BLACK], &WDLTable.back());
}

// TB are compressed with canonical Huffman code. The compressed data is divided into
// blocks of size d->sizeofBlock, and each block stores a variable number of symbols.
// Each symbol represents either a WDL or (remapped) DTZ value, or a pair of other symbols
// (recursively). If you keep expanding the symbols in a block, you end up with up to 65536
// WDL or DTZ values. Each symbol represents up to 256 values and will correspond after
// Huffman coding to at least 1 bit. So a block of 32 bytes corresponds to at most
// 32 x 8 x 256 = 65536 values. This maximum is only reached for tables that consist mostly
// of draws or mostly of wins, but such tables are actually quite common. In principle, the
// blocks in WDL tables are 64 bytes long (and will be aligned on cache lines). But for
// mostly-draw or mostly-win tables this can leave many 64-byte blocks only half-filled, so
// in such cases blocks are 32 bytes long. The blocks of DTZ tables are up to 1024 bytes long.
// The generator picks the size that leads to the smallest table. The "book" of symbols and
// Huffman codes is the same for all blocks in the table (a non-symmetric pawnless TB file
// will have one table for wtm and one for btm, a TB file with pawns will have tables per
// file a,b,c,d).
int decompress_pairs(PairsData* d, uint64_t idx)
{
    // Special case where all table positions store the same value
    if (d->flags & TBFlag::SingleValue)
        return d->minSymLen;

    // First we need to locate the right block that stores the value at index "idx".
    // Because each block n stores blockLength[n] + 1 values, the index i of the block
    // that contains the value at position idx is:
    //
    //                    for (i = -1, sum = 0; sum <= idx; i++)
    //                        sum += blockLength[i + 1] + 1;
    //
    // This can be slow, so we use SparseIndex[] populated with a set of SparseEntry that
    // point to known indices into blockLength[]. Namely SparseIndex[k] is a SparseEntry
    // that stores the blockLength[] index and the offset within that block of the value
    // with index N(k), where:
    //
    //       N(k) = k * d->span + d->span / 2      (1)

    // First step is to get the 'k' of the N(k) nearest to our idx, using defintion (1)
    uint32_t k = idx / d->span;

    // Then we read the corresponding SparseIndex[] entry
    uint32_t block = number<uint32_t, LittleEndian>(&d->sparseIndex[k].block);
    int idxOffset  = number<uint16_t, LittleEndian>(&d->sparseIndex[k].offset);

    // Now compute the difference idx - N(k). From defintion of k we know that
    //
    //       idx = k * d->span + idx % d->span    (2)
    //
    // So from (1) and (2) we can compute idx - N(K):
    int diff = idx % d->span - d->span / 2;

    // Sum to idxOffset to find the offset corresponding to our idx
    idxOffset += diff;

    // Move to previous/next block, until we reach the correct block that contains idx,
    // that is when 0 <= idxOffset <= d->blockLength[block]
    while (idxOffset < 0)
        idxOffset += d->blockLength[--block] + 1;

    while (idxOffset > d->blockLength[block])
        idxOffset -= d->blockLength[block++] + 1;

    // Finally, we find the start address of our block of canonical Huffman coded symbols
    uint32_t* ptr = (uint32_t*)(d->data + block * d->sizeofBlock);

    // Read the first 64 bits in our block. We still don't know the symbol length but
    // we know is at the beginning of this 64 bits sequence.
    uint64_t buf64 = number<uint64_t, BigEndian>(ptr); ptr += 2;
    int buf64Size = 64;
    Sym sym;

    while (true) {
        int len = 0; // This is the symbol length - d->min_sym_len

        // Now get the symbol length. For any symbol s64 of length l right-padded
        // to 64 bits holds d->base64[l-1] >= s64 >= d->base64[l] so we can find
        // the symbol length iterating through base64[].
        while (buf64 < d->base64[len])
            ++len;

        // Symbols of same length are mapped to consecutive numbers, so we can compute
        // the offset of our symbol of length len, stored at the beginning of buf64.
        sym = (buf64 - d->base64[len]) >> (64 - len - d->minSymLen);

        // Now add the value of the lowest symbol of length len to get our symbol
        sym += number<Sym, LittleEndian>(&d->lowestSym[len]);

        // If our offset is within the number of values represented by symbol sym
        // we are done...
        if (idxOffset < (int)d->symlen[sym] + 1)
            break;

        // ...otherwise update the offset and continue to iterate
        idxOffset -= d->symlen[sym] + 1;
        len += d->minSymLen; // Get the real length
        buf64 <<= len;       // Consume the just processed symbol
        buf64Size -= len;

        if (buf64Size <= 32) { // Refill the buffer
            buf64Size += 32;
            buf64 |= (uint64_t)number<uint32_t, BigEndian>(ptr++) << (64 - buf64Size);
        }
    }

    // Ok, now we have our symbol that stores d->symlen[sym] values, the score we are
    // looking for is among those values. We binary-search for it expanding the symbol
    // in a pair of left and right child symbols and continue recursively until we are
    // at a symbol of length 1 (symlen[sym] + 1 == 1), which is the value we need.
    while (d->symlen[sym]) {

        // Each btree[] entry expands in a left-handed and right-handed pair of
        // additional symbols. We keep expanding recursively picking the symbol
        // that contains our idxOffset.
        Sym sl = d->btree[sym].get<LR::Left>();

        if (idxOffset < (int)d->symlen[sl] + 1)
            sym = sl;
        else {
            idxOffset -= d->symlen[sl] + 1;
            sym = d->btree[sym].get<LR::Right>();
        }
    }

    return d->btree[sym].get<LR::Value>();
}

template<typename Entry>
bool check_dtz_stm(Entry*, File, int) { return true; }

template<>
bool check_dtz_stm(DTZEntry* entry, File f, int stm)
{
    int flags = entry->hasPawns ? entry->pawn.file[f].precomp->flags
                                : entry->piece.precomp->flags;

    return   (flags & TBFlag::STM) == stm
          || ((entry->key == entry->key2) && !entry->hasPawns);
}

// DTZ scores are sorted by frequency of occurrence and then assigned the
// values 0, 1, 2, ... in order of decreasing frequency. This is done for each
// of the four WDLScore values. The mapping information necessary to reconstruct
// the original values is stored in the TB file and read during map[] init.
template<typename Entry>
int map_score(Entry*, File, int value, WDLScore) { return value - 2; }

template<>
int map_score(DTZEntry* entry, File f, int value, WDLScore wdl)
{
    const int WDLMap[]  = { 1, 3, 0, 2, 0 };

    int flags = entry->hasPawns ? entry->pawn.file[f].precomp->flags
                                : entry->piece.precomp->flags;

    uint8_t* map = entry->hasPawns ? entry->pawn.map
                                   : entry->piece.map;

    uint16_t* idx = entry->hasPawns ? entry->pawn.file[f].map_idx
                                    : entry->piece.map_idx;
    if (flags & TBFlag::Mapped)
        value = map[idx[WDLMap[wdl + 2]] + value];

    // DTZ tables store distance to zero in number of moves but
    // under some conditions we want to return plies, so we have
    // to multiply score by 2.
    if (   (wdl == WDLWin  && !(flags & TBFlag::WinPlies))
        || (wdl == WDLLoss && !(flags & TBFlag::LossPlies))
        ||  wdl == WDLCursedWin
        ||  wdl == WDLCursedLoss)
        value *= 2;

    return value + 1;
}

// Compute a unique index out of a position and use it to probe the TB file. To
// encode k pieces of same type and color, first sort the pieces by square in
// ascending order s1 <= s2 <= ... <= sk then compute the unique index as:
//
//      idx = Binomial[1][s1] + Binomial[2][s2] + ... + Binomial[k][sk]
//
template<typename Entry>
uint64_t probe_table(const Position& pos,  Entry* entry, WDLScore wdl = WDLDraw, ProbeState* result = nullptr)
{
    Square squares[TBPIECES];
    Piece pieces[TBPIECES];
    uint64_t idx;
    int stm, next = 0, flipColor = 0, flipSquares = 0, size = 0, leadPawnsCnt = 0;
    PairsData* precomp;
    Bitboard b, leadPawns = 0;
    File tbFile = FILE_A;

    // A given TB entry like KRK has associated two material keys: KRvk and Kvkr.
    // If both sides have the same pieces we have a symmetric material and the
    // keys are equal. The stored TB entry is calculated always with WHITE side
    // to move and if the position to lookup has instead BLACK to move, we need
    // to switch color and flip the squares before the lookup:
    if (entry->key == entry->key2) {
        flipColor = pos.side_to_move() * 8;     // Switch color
        flipSquares = pos.side_to_move() * 070; // Vertical flip: SQ_A8 -> SQ_A1
        stm = WHITE;
    }
    // In case of sides with different pieces, if the position to look up has a
    // different key form the stored one (entry->key), then we have to switch
    // color and flip the squares:
    else {
        flipColor   = (pos.material_key() != entry->key) * 8;
        flipSquares = (pos.material_key() != entry->key) * 070;

        // TB entry is stored with WHITE as stronger side, so side to move has
        // to be flipped accordingly, for example Kvkr (white to move) maps to
        // KRvk (black to move).
        stm = (pos.material_key() != entry->key) ^ pos.side_to_move();
    }

    // For pawns, TB files store separate tables according if leading pawn is on
    // file a, b, c or d after reordering. To determine which of the 4 tables
    // must be probed we pick the file of the pawn with maximum MapPawns[].
    if (entry->hasPawns) {
        Piece pc = Piece(item(entry->pawn, 0, 0).precomp->pieces[0] ^ flipColor);

        assert(type_of(pc) == PAWN);

        leadPawns = b = pos.pieces(color_of(pc), PAWN);
        while (b)
            squares[size++] = pop_lsb(&b) ^ flipSquares;

        leadPawnsCnt = size;

        std::swap(squares[0], *std::max_element(squares, squares + leadPawnsCnt, pawns_comp));

        tbFile = file_of(squares[0]);
        if (tbFile > FILE_D)
            tbFile = file_of(squares[0] ^ 7); // Horizontal flip: SQ_H1 -> SQ_A1

        precomp = item(entry->pawn, stm, tbFile).precomp;
    } else
        precomp = item(entry->piece, stm, 0).precomp;

    // DTZ tables are one-sided, i.e. they store positions only for white to
    // move or only for black to move, so check for side to move to be stm,
    // early exit otherwise.
    if (    std::is_same<Entry, DTZEntry>::value
        && !check_dtz_stm(entry, tbFile, stm)) {
        *result = CHANGE_STM;
        return 0;
    }

    // Now we are ready to get all the position pieces (but the lead pawns) and
    // directly map them to the correct color and square.
    b = pos.pieces() ^ leadPawns;
    for ( ; b; ++size) {
        Square sq = pop_lsb(&b);
        squares[size] = sq ^ flipSquares;
        pieces[size] = Piece(pos.piece_on(sq) ^ flipColor);
    }

    // Then we reorder the pieces to have the same sequence as the one stored
    // in precomp->pieces[i]. The sequence ensures the best compression.
    for (int i = leadPawnsCnt; i < size; ++i)
        for (int j = i; j < size; ++j)
            if (precomp->pieces[i] == pieces[j])
            {
                std::swap(pieces[i], pieces[j]);
                std::swap(squares[i], squares[j]);
                break;
            }

    // Now we map again the squares so that the square of the lead piece is in
    // the triangle A1-D1-D4. We take care that the condition on the diagonal
    // flip is checked after horizontal and vertical flips are already done.
    if (file_of(squares[0]) > FILE_D)
        for (int i = 0; i < size; ++i)
            squares[i] ^= 7; // Horizontal flip: SQ_H1 -> SQ_A1

    // Encode leading pawns starting with the one with minimum MapPawns[] and
    // proceeding in ascending order.
    if (entry->hasPawns) {
        idx = LeadPawnIdx[leadPawnsCnt - 1][squares[0]];

        std::sort(squares + 1, squares + leadPawnsCnt, pawns_comp);

        for (int i = 1; i < leadPawnsCnt; ++i)
            idx += Binomial[i][MapPawns[squares[i]]];

        next = leadPawnsCnt;
        goto encode_remaining; // With pawns we have finished special treatments
    }

    if (rank_of(squares[0]) > RANK_4)
        for (int i = 0; i < size; ++i)
            squares[i] ^= 070; // Vertical flip: SQ_A8 -> SQ_A1

    // Look for the first piece not on the A1-D4 diagonal and ensure it is
    // mapped below the diagonal.
    for (int i = 0; i < size; ++i) {
        if (!off_A1H8(squares[i]))
            continue;

        if (off_A1H8(squares[i]) > 0 && i < (entry->hasUniquePieces ? 3 : 2))
            for (int j = i; j < size; ++j) // A1-H8 diagonal flip: SQ_A3 -> SQ_C3
                squares[j] = Square(((squares[j] >> 3) | (squares[j] << 3)) & 63);
        break;
    }

    // The encoding function maps a position to its index into the table.
    // Suppose we have KRvK. Let's say the pieces are on square numbers wK, wR
    // and bK (each 0...63). The simplest way to map this position to an index
    // is like this:
    //
    //   index = wK * 64*64 + wR * 64 + bK;
    //
    // But this way the TB is going to have 64*64*64 = 262144 positions, with
    // lots of positions being equivalent (because they are mirrors of each
    // other) and lots of positions being invalid (two pieces on one square,
    // adjacent kings, etc.).
    // Usually the first step is to take the wK and bK together. There are just
    // 462 ways legal and not-mirrored ways to place the wK and bK on the board.
    // Once we have placed the wK and bK, there are 62 squares left for the wR
    // Mapping its square from 0..63 to 0..61 can be done like:
    //
    //   wR -= (wR > wK) + (wR > bK);
    //
    // In words: if wR "comes later" than wK, we deduct 1, and the same if wR
    // "comes later" than bK. In case of two same pieces like KRRvK we want to
    // place the two Rs "together". If we have 62 squares left, we can place two
    // Rs "together" in 62*61/2 ways.

    // In case we have at least 3 unique pieces (inlcuded kings) we encode them
    // together.
    if (entry->hasUniquePieces) {

        int adjust1 =  squares[1] > squares[0];
        int adjust2 = (squares[2] > squares[0]) + (squares[2] > squares[1]);

        // MapA1D1D4[] maps the b1-d1-d3 triangle to 0...5. There are 63 squares
        // for second piece and and 62 (mapped to 0...61) for the third.
        if (off_A1H8(squares[0]))
            idx =   MapA1D1D4[squares[0]] * 63 * 62
                 + (squares[1] - adjust1) * 62
                 +  squares[2] - adjust2;

        // First piece is on diagonal: map to 6, rank_of() maps a1-d4 diagonal
        // to 0...3 and MapB1H1H7[] maps the b1-h1-h7 triangle to 0..27
        else if (off_A1H8(squares[1]))
            idx =                      6 * 63 * 62
                 + rank_of(squares[0])   * 28 * 62
                 + MapB1H1H7[squares[1]] * 62
                 + squares[2] - adjust2;

        // First 2 pieces are on the diagonal a1-h8
        else if (off_A1H8(squares[2]))
            idx =  6 * 63 * 62 + 4 * 28 * 62
                 +  rank_of(squares[0])        * 7 * 28
                 + (rank_of(squares[1]) - adjust1) * 28
                 +  MapB1H1H7[squares[2]];

        // All 3 pieces on the diagonal a1-h8
        else
            idx = 6 * 63 * 62 + 4 * 28 * 62 + 4 * 7 * 28
                 +  rank_of(squares[0])         * 7 * 6
                 + (rank_of(squares[1]) - adjust1)  * 6
                 + (rank_of(squares[2]) - adjust2);

        next = 3; // Continue encoding form piece[3]
    } else {
        // We don't have at least 3 unique pieces, like in KRRvKBB, just map
        // the kings.
        idx = MapKK[MapA1D1D4[squares[0]]][squares[1]];
        next = 2;
    }

encode_remaining:
    idx *= precomp->groupSize[0];

    // Reorder remainig pawns then pieces according to square, in ascending order
    int remainingPawns = entry->hasPawns ? entry->pawn.pawnCount[1] : 0;

    while (next < size) {

        int end = next + (remainingPawns ? remainingPawns : precomp->groupLen[next]);

        std::sort(squares + next, squares + end);

        uint64_t s = 0;

        // Map squares to lower index if "come later" than previous (as done earlier for pieces)
        for (int i = next; i < end; ++i) {
            int adjust = 0;

            for (int j = 0; j < next; ++j)
                adjust += squares[i] > squares[j];

            s += Binomial[i - next + 1][squares[i] - adjust - (remainingPawns ? 8 : 0)];
        }

        remainingPawns = 0;
        idx += s * precomp->groupSize[next];
        next = end;
    }

    // Now that we have the index, decompress the pair and get the score
    return map_score(entry, tbFile, decompress_pairs(precomp, idx), wdl);
}

// Group together pieces that will be encoded together. For instance in
// KRKN the encoder will default on '111', so the groups will be (3,1)
// and for easy of parsing the resulting groupLen[] will be (3, 0, 0, 1).
// In case of pawns, they will be encoded as first, starting with the
// leading ones, then the remaining pieces. Then calculate the size, in
// number of possible combinations, needed to store them in the TB file.
template<typename T>
uint64_t set_groups(T& e, PairsData* d, int order[], File f)
{
    for (int i = 0; i < e.pieceCount; ++i) // Broken MSVC zero-init
        d->groupLen[i] = 0;

    // Set leading pawns or pieces
    int len = d->groupLen[0] =         e.hasPawns ? e.pawn.pawnCount[0]
                              : e.hasUniquePieces ? 3 : 2;
    // Set remaining pawns, if any
    if (e.hasPawns)
        len += d->groupLen[len] = e.pawn.pawnCount[1];

    // Set remaining pieces. If 2 pieces are equal, they are grouped together.
    // They are ensured to be consecutive in pieces[].
    for (int k = len ; k < e.pieceCount; k += d->groupLen[k])
        for (int j = k; j < e.pieceCount && d->pieces[j] == d->pieces[k]; ++j)
            ++d->groupLen[k];

    // Now calculate the size needed for each group, according to the order
    // given by order[]. In general the order is a per-table value and could
    // not follow the canonical leading pawns -> remainig pawns -> pieces.
    int freeSquares = 64 - len;
    uint64_t size = 1;

    for (int k = 0; len < e.pieceCount || k == order[0] || k == order[1]; ++k)
        if (k == order[0]) // Leading pawns or pieces
        {
            d->groupSize[0] = size;

            size *=         e.hasPawns ? LeadPawnsGroupSize[d->groupLen[0] - 1][f]
                   : e.hasUniquePieces ? 31332 : 462;
        }
        else if (k == order[1]) // Remaining pawns
        {
            d->groupSize[d->groupLen[0]] = size;
            size *= Binomial[d->groupLen[d->groupLen[0]]][48 - d->groupLen[0]];
        }
        else // Remainig pieces
        {
            d->groupSize[len] = size;
            size *= Binomial[d->groupLen[len]][freeSquares];
            freeSquares -= d->groupLen[len];
            len += d->groupLen[len];
        }

    return size;
}

uint8_t set_symlen(PairsData* d, Sym s, std::vector<bool>& visited)
{
    visited[s] = true; // We can set it now because tree is acyclic
    Sym sr = d->btree[s].get<LR::Right>();

    if (sr == 0xFFF)
        return 0;

    Sym sl = d->btree[s].get<LR::Left>();

    if (!visited[sl])
        d->symlen[sl] = set_symlen(d, sl, visited);

    if (!visited[sr])
        d->symlen[sr] = set_symlen(d, sr, visited);

    return d->symlen[sl] + d->symlen[sr] + 1;
}

uint8_t* set_sizes(PairsData* d, uint8_t* data, uint64_t tb_size)
{
    d->flags = *data++;

    if (d->flags & TBFlag::SingleValue) {
        d->blocksNum = d->span =
        d->blockLengthSize = d->sparseIndexSize = 0; // Broken MSVC zero-init
        d->minSymLen = *data++; // Here we store the single value
        return data;
    }

    d->sizeofBlock = 1ULL << *data++;
    d->span = 1ULL << *data++;
    d->sparseIndexSize = (tb_size + d->span - 1) / d->span; // Round up
    int padding = number<uint8_t, LittleEndian>(data++);
    d->blocksNum = number<uint32_t, LittleEndian>(data); data += sizeof(uint32_t);
    d->blockLengthSize = d->blocksNum + padding; // Padded to ensure SparseIndex[]
                                                 // does not point out of range.
    d->maxSymLen = *data++;
    d->minSymLen = *data++;
    d->lowestSym = (Sym*)data;
    d->base64.resize(d->maxSymLen - d->minSymLen + 1);

    // The canonical code is ordered such that longer symbols (in terms of
    // the number of bits of their Huffman code) have lower numeric value,
    // so that d->lowestSym[i] >= d->lowestSym[i+1] (when read as LittleEndian).
    // Starting from this we compute a base64[] table indexed by symbol length
    // and containing 64 bit values so that d->base64[i] >= d->base64[i+1]
    for (int i = d->base64.size() - 2; i >= 0; --i) {
        d->base64[i] = (d->base64[i + 1] + number<Sym, LittleEndian>(&d->lowestSym[i])
                                         - number<Sym, LittleEndian>(&d->lowestSym[i + 1])) / 2;

        assert(d->base64[i] * 2 >= d->base64[i+1]);
    }

    // Now left-shift by an amount so that d->base64[i] gets shifted 1 bit more
    // than d->base64[i+1] and given the above assert condition, we ensure that
    // d->base64[i] >= d->base64[i+1]. Moreover for any symbol s64 of length i
    // and right-padded to 64 bits holds d->base64[i-1] >= s64 >= d->base64[i].
    for (size_t i = 0; i < d->base64.size(); ++i)
        d->base64[i] <<= 64 - i - d->minSymLen; // Right-padding to 64 bits

    data += d->base64.size() * sizeof(Sym);
    d->symlen.resize(number<uint16_t, LittleEndian>(data)); data += sizeof(uint16_t);
    d->btree = (LR*)data;

    std::vector<bool> visited(d->symlen.size());

    for (Sym sym = 0; sym < d->symlen.size(); ++sym)
        if (!visited[sym])
            d->symlen[sym] = set_symlen(d, sym, visited);

    return data + d->symlen.size() * sizeof(LR) + (d->symlen.size() & 1);
}

template<typename T>
uint8_t* set_dtz_map(WDLEntry&, T&, uint8_t*, File) { return nullptr; }

template<typename T>
uint8_t* set_dtz_map(DTZEntry&, T& p, uint8_t* data, File maxFile)
{
    p.map = data;

    for (File f = FILE_A; f <= maxFile; ++f) {
        if (item(p, 0, f).precomp->flags & TBFlag::Mapped)
            for (int i = 0; i < 4; ++i) { // Sequence like 3,x,x,x,1,x,0,2,x,x
                item(p, 0, f).map_idx[i] = (uint16_t)(data - p.map + 1);
                data += *data + 1;
            }
    }

    return data += (uintptr_t)data & 1; // Word alignment
}

template<typename Entry, typename T>
void do_init(Entry& e, T& p, uint8_t* data)
{
    const bool IsWDL = std::is_same<Entry, WDLEntry>::value;

    PairsData* d;
    uint64_t tb_size[8];

    enum { Split = 1, HasPawns = 2 };

    uint8_t flags = *data++;

    assert(e.hasPawns        == !!(flags & HasPawns));
    assert((e.key != e.key2) == !!(flags & Split));

    const int Sides = IsWDL && (e.key != e.key2) ? 2 : 1;
    const File MaxFile = e.hasPawns ? FILE_D : FILE_A;

    bool pp = e.hasPawns && e.pawn.pawnCount[1]; // Pawns on both sides

    assert(!pp || e.pawn.pawnCount[0]);

    for (File f = FILE_A; f <= MaxFile; ++f) {

        for (int i = 0; i < Sides; i++)
            item(p, i, f).precomp = new PairsData();

        int order[][2] = { { *data & 0xF, pp ? *(data + 1) & 0xF : 0xF },
                           { *data >>  4, pp ? *(data + 1) >>  4 : 0xF } };
        data += 1 + pp;

        for (int k = 0; k < e.pieceCount; ++k, ++data)
            for (int i = 0; i < Sides; i++)
                item(p, i, f).precomp->pieces[k] = Piece(i ? *data >>  4 : *data & 0xF);

        for (int i = 0; i < Sides; ++i)
            tb_size[Sides * f + i] = set_groups(e, item(p, i, f).precomp, order[i], f);
    }

    data += (uintptr_t)data & 1; // Word alignment

    for (File f = FILE_A; f <= MaxFile; ++f)
        for (int i = 0; i < Sides; i++)
            data = set_sizes(item(p, i, f).precomp, data, tb_size[Sides * f + i]);

    if (!IsWDL)
        data = set_dtz_map(e, p, data, MaxFile);

    for (File f = FILE_A; f <= MaxFile; ++f)
        for (int i = 0; i < Sides; i++) {
            (d = item(p, i, f).precomp)->sparseIndex = (SparseEntry*)data;
            data += d->sparseIndexSize * sizeof(SparseEntry) ;
        }

    for (File f = FILE_A; f <= MaxFile; ++f)
        for (int i = 0; i < Sides; i++) {
            (d = item(p, i, f).precomp)->blockLength = (uint16_t*)data;
            data += d->blockLengthSize * sizeof(uint16_t);
        }

    for (File f = FILE_A; f <= MaxFile; ++f)
        for (int i = 0; i < Sides; i++) {
            data = (uint8_t*)(((uintptr_t)data + 0x3F) & ~0x3F); // 64 byte alignment
            (d = item(p, i, f).precomp)->data = data;
            data += d->blocksNum * d->sizeofBlock;
        }
}

template<typename Entry>
bool init(Entry& e, const std::string& fname)
{
    const uint8_t* MAGIC = std::is_same<Entry, DTZEntry>::value ? DTZ_MAGIC : WDL_MAGIC;

    uint8_t* data = TBFile(fname).map(&e.baseAddress, &e.mapping, MAGIC);
    if (!data)
        return false;

    e.hasPawns ? do_init(e, e.pawn, data) : do_init(e, e.piece, data);
    return true;
}

WDLScore probe_wdl_table(Position& pos, ProbeState* result)
{
    Key key = pos.material_key();

    if (!(pos.pieces() ^ pos.pieces(KING)))
        return WDLDraw; // KvK

    WDLEntry* entry = WDLHash[key];
    if (!entry) {
        *result = FAIL;
        return WDLDraw;
    }

    // Init table at first access attempt. Special care to avoid
    // one thread reads ready == 1 while the other is still in
    // init(), this could happen due to compiler reordering.
    if (!entry->ready.load(std::memory_order_acquire)) {
        std::unique_lock<Mutex> lk(TB_mutex);
        if (!entry->ready.load(std::memory_order_relaxed)) {
            std::string fname = pos_code(pos, entry->key != key) + ".rtbw";
            if (!init(*entry, fname)) {
                // Was ptr2->key = 0ULL;  Just leave !ptr->ready condition
                *result = FAIL;
                return WDLDraw;
            }
            entry->ready.store(1, std::memory_order_release);
        }
    }

    return (WDLScore)probe_table(pos, entry);
}

int probe_dtz_table(const Position& pos, WDLScore wdl, ProbeState* result)
{
    Key key = pos.material_key();

    if (DTZTable.front().key != key && DTZTable.front().key2 != key) {

        // Enforce "Most Recently Used" (MRU) order for DTZ list
        for (auto it = DTZTable.begin(); it != DTZTable.end(); ++it)
            if (it->key == key || it->key2 == key) {
                // Move to front without deleting the element
                DTZTable.splice(DTZTable.begin(), DTZTable, it);
                break;
            }

        // If still not found, add a new one
        if (DTZTable.front().key != key && DTZTable.front().key2 != key) {

            WDLEntry* wdlEntry = WDLHash[key];
            if (!wdlEntry) {
                *result = FAIL;
                return 0;
            }

            DTZTable.push_front(DTZEntry(*wdlEntry));

            std::string fname = pos_code(pos, wdlEntry->key != key) + ".rtbz";
            if (!init(DTZTable.front(), fname)) {
                // In case file is not found init() fails, but we leave
                // the entry so to avoid rechecking at every probe (same
                // functionality as WDL case).
                // FIXME: This is different form original functionality!
                /* DTZTable.pop_front(); */
                *result = FAIL;
                return 0;
            }

            // Keep list size within 64 entries
            // FIXME remove it when we will know what we are doing
            if (DTZTable.size() > 64)
               DTZTable.pop_back();
        }
    }

    if (!DTZTable.front().baseAddress) {
        *result = FAIL;
        return 0;
    }

    return probe_table(pos, &DTZTable.front(), wdl, result);
}

// For a position where the side to move has a winning capture it is not necessary
// to store a winning value so the generator treats such positions as "don't cares"
// and tries to assign to it a value that improves the compression ratio. Similarly,
// if the side to move has a drawing capture, then the position is at least drawn.
// If the position is won, then the TB needs to store a win value. But if the
// position is drawn, the TB may store a loss value if that is better for compression.
// All of this means that during probing, the engine must look at captures and probe
// their results and must probe the position itself. The "best" result of these
// probes is the correct result for the position.
// DTZ table don't store values when a following move is a zeroing winning move
// (winning capture or winning pawn move). Also DTZ store wrong values for positions
// where the best move is an ep-move (even if losing). So in all these cases set
// the state to ZEROING_MOVE.
template<bool CheckZeroingMoves = false>
WDLScore search(Position& pos, WDLScore alpha, WDLScore beta, ProbeState* result)
{
    WDLScore value;
    StateInfo st;
    CheckInfo ci(pos);

    auto moveList = MoveList<LEGAL>(pos);
    size_t totalCount = moveList.size();
    size_t moveCount = 0;
    for (const Move& move : moveList)
    {
        if (   !pos.capture(move)
            && (!CheckZeroingMoves || type_of(pos.moved_piece(move)) != PAWN))
            continue;

        moveCount++;

        pos.do_move(move, st, pos.gives_check(move, ci));
        value = -search(pos, -beta, -alpha, result);
        pos.undo_move(move);

        if (*result == FAIL)
            return WDLDraw;

        if (value >= beta)
        {
            *result = ZEROING_BEST_MOVE; // Winning DTZ-zeroing move
            return value;
        }

        if (value > alpha)
            alpha = value;
    }

    // In case we have already searched all the legal moves we don't have to probe
    // the TB because the stored score could be wrong. For instance TB tables
    // do not contain information on position with ep rights, so in this case
    // the result of probe_wdl_table is wrong. Also in case of only capture
    // moves, for instance here 4K3/4q3/6p1/2k5/6p1/8/8/8 w - - 0 7, we have to
    // return with ZEROING_BEST_MOVE set.
    bool noMoreMoves = (moveCount && moveCount == totalCount);

    if (noMoreMoves)
        value = alpha;
    else
    {
        value = probe_wdl_table(pos, result);

        if (*result == FAIL)
            return WDLDraw;
    }

    // Here alpha stores the best value of the ply-1 search, note that in case
    // we have already searched all the possible moves alpha == value.
    if (alpha >= value)
        return *result = (alpha > WDLDraw || noMoreMoves ? ZEROING_BEST_MOVE : OK), alpha;

    return *result = OK, value;
}

} // namespace

void Tablebases::init(const std::string& paths)
{
    DTZTable.clear();
    WDLTable.clear();
    WDLHash.clear();

    MaxCardinality = 0;
    TBPaths = paths;

    if (TBPaths.empty() || TBPaths == "<empty>")
        return;

    // Init MapB1H1H7[] that encodes a square below a1-h8 diagonal to 0..27
    int code = 0;
    for (Square s = SQ_A1; s <= SQ_H8; ++s)
        if (off_A1H8(s) < 0)
            MapB1H1H7[s] = code++;

    // Init MapA1D1D4[] that encodes a square in the a1-d1-d4 triangle to 0..9
    std::vector<Square> diagonal;
    code = 0;
    for (Square s = SQ_A1; s <= SQ_D4; ++s)
        if (off_A1H8(s) < 0 && file_of(s) <= FILE_D)
            MapA1D1D4[s] = code++;

        else if (!off_A1H8(s) && file_of(s) <= FILE_D)
            diagonal.push_back(s);

    // Diagonal squares are encoded as last ones
    for (auto s : diagonal)
        MapA1D1D4[s] = code++;

    // Init MapKK[] that encodes all the 461 possible legal positions of two
    // kings where the first is in the a1-d1-d4 triangle. If the first king is
    // on the a1-d4 diagonal, the other shall not to be above the a1-h8 diagonal.
    std::vector<std::pair<int, Square>> bothOnDiagonal;
    code = 0;
    for (int idx = 0; idx < 10; idx++)
        for (Square s1 = SQ_A1; s1 <= SQ_D4; ++s1)
            if (MapA1D1D4[s1] == idx && (idx || s1 == SQ_B1)) // SQ_B1 is mapped to 0
                for (Square s2 = SQ_A1; s2 <= SQ_H8; ++s2)
                    if ((StepAttacksBB[KING][s1] | s1) & s2)
                        continue; // Illegal position

                    else if (!off_A1H8(s1) && off_A1H8(s2) > 0)
                        continue; // First on diagonal, second above

                    else if (!off_A1H8(s1) && !off_A1H8(s2))
                        bothOnDiagonal.push_back(std::make_pair(idx, s2));

                    else
                        MapKK[idx][s2] = code++;

    // Legal positions with both kings on diagonal are encoded as last ones
    for (auto p : bothOnDiagonal)
        MapKK[p.first][p.second] = code++;

    // Init Binomial[] with the Binomial Coefficents using Pascal rule. There
    // are Binomial[k][n] ways to choose k elements from a set of n elements.
    Binomial[0][0] = 1;

    for (int n = 1; n < 64; n++) // Squares
        for (int k = 0; k < 6 && k <= n; ++k) // Pieces
            Binomial[k][n] =  (k > 0 ? Binomial[k - 1][n - 1] : 0)
                            + (k < n ? Binomial[k    ][n - 1] : 0);

    // MapPawns[s] encodes squares a2-h7 to 0..47. It is the number of possible
    // available squares when the leading one is in 's'. Moreover the pawn with
    // highest MapPawns[] is the leading pawn, the one nearest the edge and,
    // among pawns with same file, the one with lowest rank.
    int availableSquares = 47; // Available squares when lead pawn is in a2

    // Init the tables for the encoding of leading pawns group: with 6-men TB we
    // can have up to 4 leading pawns (KPPPPK).
    for (int leadPawnsCnt = 1; leadPawnsCnt <= 4; ++leadPawnsCnt)
        for (File f = FILE_A; f <= FILE_D; ++f)
        {
            // Restart the index at every file because TB table is splitted
            // by file, so we can reuse the same index for different files.
            int idx = 0;

            // Sum all possible combinations for a given file, starting with
            // the leading pawn on rank 2 and increasing the rank.
            for (Rank r = RANK_2; r <= RANK_7; ++r)
            {
                Square sq = make_square(f, r);

                // Compute MapPawns[] at first pass.
                // If sq is the leading pawn square, any other pawn cannot be
                // below or more toward the edge of sq. There are 47 available
                // squares when sq = a2 and reduced by 2 for any rank increase
                // due to mirroring: sq == a3 -> no a2, h2, so MapPawns[a3] = 45
                if (leadPawnsCnt == 1)
                {
                    MapPawns[sq] = availableSquares--;
                    MapPawns[sq ^ 7] = availableSquares--; // Horizontal flip
                }
                LeadPawnIdx[leadPawnsCnt - 1][sq] = idx;
                idx += Binomial[leadPawnsCnt - 1][MapPawns[sq]];
            }
            // After a file is traversed, store the cumulated per-file index
            LeadPawnsGroupSize[leadPawnsCnt - 1][f] = idx;
        }

    for (PieceType p1 = PAWN; p1 < KING; ++p1) {
        WDLHash.insert({KING, p1, KING});

        for (PieceType p2 = PAWN; p2 <= p1; ++p2) {
            WDLHash.insert({KING, p1, p2, KING});
            WDLHash.insert({KING, p1, KING, p2});

            for (PieceType p3 = PAWN; p3 < KING; ++p3)
                WDLHash.insert({KING, p1, p2, KING, p3});

            for (PieceType p3 = PAWN; p3 <= p2; ++p3) {
                WDLHash.insert({KING, p1, p2, p3, KING});

                for (PieceType p4 = PAWN; p4 <= p3; ++p4)
                    WDLHash.insert({KING, p1, p2, p3, p4, KING});

                for (PieceType p4 = PAWN; p4 < KING; ++p4)
                    WDLHash.insert({KING, p1, p2, p3, KING, p4});
            }

            for (PieceType p3 = PAWN; p3 <= p1; ++p3)
                for (PieceType p4 = PAWN; p4 <= (p1 == p3 ? p2 : p3); ++p4)
                    WDLHash.insert({KING, p1, p2, KING, p3, p4});
        }
    }

    std::cerr << "info string Found " << WDLTable.size() << " tablebases" << std::endl;
}

// Probe the WDL table for a particular position.
// If *result != FAIL, the probe was successful.
// The return value is from the point of view of the side to move:
// -2 : loss
// -1 : loss, but draw under 50-move rule
//  0 : draw
//  1 : win, but draw under 50-move rule
//  2 : win
WDLScore Tablebases::probe_wdl(Position& pos, ProbeState* result)
{
    *result = OK;
    return search(pos, WDLLoss, WDLWin, result);
}

// Probe the DTZ table for a particular position.
// If *result != FAIL, the probe was successful.
// The return value is from the point of view of the side to move:
//         n < -100 : loss, but draw under 50-move rule
// -100 <= n < -1   : loss in n ply (assuming 50-move counter == 0)
//         0        : draw
//     1 < n <= 100 : win in n ply (assuming 50-move counter == 0)
//   100 < n        : win, but draw under 50-move rule
//
// The return value n can be off by 1: a return value -n can mean a loss
// in n+1 ply and a return value +n can mean a win in n+1 ply. This
// cannot happen for tables with positions exactly on the "edge" of
// the 50-move rule.
//
// This implies that if dtz > 0 is returned, the position is certainly
// a win if dtz + 50-move-counter <= 99. Care must be taken that the engine
// picks moves that preserve dtz + 50-move-counter <= 99.
//
// If n = 100 immediately after a capture or pawn move, then the position
// is also certainly a win, and during the whole phase until the next
// capture or pawn move, the inequality to be preserved is
// dtz + 50-movecounter <= 100.
//
// In short, if a move is available resulting in dtz + 50-move-counter <= 99,
// then do not accept moves leading to dtz + 50-move-counter == 100.
int Tablebases::probe_dtz(Position& pos, ProbeState* result)
{
    *result = OK;
    WDLScore wdl = search<true>(pos, WDLLoss, WDLWin, result);

    if (*result == FAIL)
        return 0;

    if (wdl == WDLDraw) // DTZ tables don't store draws
        return 0;

    // DTZ table stores a 'don't care' value in this case, or even a plain wrong
    // one as in case the best move is a losing ep, so it cannot be probed.
    if (*result == ZEROING_BEST_MOVE)
        return zeroing_move_dtz(wdl);

    int dtz = probe_dtz_table(pos, wdl, result); // Probe the table!

    if (*result != CHANGE_STM)
        return (dtz + 100 * (wdl == WDLCursedLoss || wdl == WDLCursedWin)) * sign_of(wdl);

    // DTZ stores results for the other side, so we need to do a 1-ply search and
    // find the winning move that minimizes DTZ.
    StateInfo st;
    CheckInfo ci(pos);
    int minDTZ = 0xFFFF;

    for (const Move& move : MoveList<LEGAL>(pos))
    {
        bool zeroing = pos.capture(move) || type_of(pos.moved_piece(move)) == PAWN;

        pos.do_move(move, st, pos.gives_check(move, ci));

        // For zeroing moves we want the dtz of the move _before_ doing it,
        // otherwise we will get the dtz of the next move sequence. Search the
        // position after the move to get the score sign (because even in a
        // winning position we could make a losing capture or going for a draw).
        dtz = zeroing ? -zeroing_move_dtz(search(pos, WDLLoss, WDLWin, result))
                      : -probe_dtz(pos, result);

        pos.undo_move(move);

        if (*result == FAIL)
            return 0;

        // Skip the draws and if we are winning only pick positive dtz
        if (dtz < minDTZ && sign_of(dtz) == sign_of(wdl))
            minDTZ = dtz;
    }

    // Convert result from 1-ply search. Special handle a mate position, when
    // there are no legal moves. Return value is somewhat arbitrary, so stick
    // to the original TB code that returns -1 in this case.
    return minDTZ == 0xFFFF ? - 1 : minDTZ + sign_of(minDTZ);
}

// Check whether there has been at least one repetition of positions
// since the last capture or pawn move.
static int has_repeated(StateInfo *st)
{
    while (1) {
        int i = 4, e = std::min(st->rule50, st->pliesFromNull);

        if (e < i)
            return 0;

        StateInfo *stp = st->previous->previous;

        do {
            stp = stp->previous->previous;

            if (stp->key == st->key)
                return 1;

            i += 2;
        } while (i <= e);

        st = st->previous;
    }
}

// Use the DTZ tables to filter out moves that don't preserve the win or draw.
// If the position is lost, but DTZ is fairly high, only keep moves that
// maximise DTZ.
//
// A return value false indicates that not all probes were successful and that
// no moves were filtered out.
bool Tablebases::root_probe(Position& pos, Search::RootMoves& rootMoves, Value& score)
{
    ProbeState result;
    int dtz = probe_dtz(pos, &result);

    if (result == FAIL)
        return false;

    StateInfo st;
    CheckInfo ci(pos);

    // Probe each move
    for (size_t i = 0; i < rootMoves.size(); ++i) {
        Move move = rootMoves[i].pv[0];
        pos.do_move(move, st, pos.gives_check(move, ci));
        int v = 0;

        if (pos.checkers() && dtz > 0) {
            ExtMove s[MAX_MOVES];

            if (generate<LEGAL>(pos, s) == s)
                v = 1;
        }

        if (!v) {
            if (st.rule50 != 0) {
                v = -probe_dtz(pos, &result);

                if (v > 0)
                    ++v;
                else if (v < 0)
                    --v;
            } else {
                v = -probe_wdl(pos, &result);
                v = wdl_to_dtz[v + 2];
            }
        }

        pos.undo_move(move);

        if (result == FAIL)
            return false;

        rootMoves[i].score = (Value)v;
    }

    // Obtain 50-move counter for the root position.
    // In Stockfish there seems to be no clean way, so we do it like this:
    int cnt50 = st.previous->rule50;

    // Use 50-move counter to determine whether the root position is
    // won, lost or drawn.
    int wdl = 0;

    if (dtz > 0)
        wdl = (dtz + cnt50 <= 100) ? 2 : 1;
    else if (dtz < 0)
        wdl = (-dtz + cnt50 <= 100) ? -2 : -1;

    // Determine the score to report to the user.
    score = WDL_to_value[wdl + 2];

    // If the position is winning or losing, but too few moves left, adjust the
    // score to show how close it is to winning or losing.
    // NOTE: int(PawnValueEg) is used as scaling factor in score_to_uci().
    if (wdl == 1 && dtz <= 100)
        score = (Value)(((200 - dtz - cnt50) * int(PawnValueEg)) / 200);
    else if (wdl == -1 && dtz >= -100)
        score = -(Value)(((200 + dtz - cnt50) * int(PawnValueEg)) / 200);

    // Now be a bit smart about filtering out moves.
    size_t j = 0;

    if (dtz > 0) { // winning (or 50-move rule draw)
        int best = 0xffff;

        for (size_t i = 0; i < rootMoves.size(); ++i) {
            int v = rootMoves[i].score;

            if (v > 0 && v < best)
                best = v;
        }

        int max = best;

        // If the current phase has not seen repetitions, then try all moves
        // that stay safely within the 50-move budget, if there are any.
        if (!has_repeated(st.previous) && best + cnt50 <= 99)
            max = 99 - cnt50;

        for (size_t i = 0; i < rootMoves.size(); ++i) {
            int v = rootMoves[i].score;

            if (v > 0 && v <= max)
                rootMoves[j++] = rootMoves[i];
        }
    } else if (dtz < 0) { // losing (or 50-move rule draw)
        int best = 0;

        for (size_t i = 0; i < rootMoves.size(); ++i) {
            int v = rootMoves[i].score;

            if (v < best)
                best = v;
        }

        // Try all moves, unless we approach or have a 50-move rule draw.
        if (-best * 2 + cnt50 < 100)
            return true;

        for (size_t i = 0; i < rootMoves.size(); ++i) {
            if (rootMoves[i].score == best)
                rootMoves[j++] = rootMoves[i];
        }
    } else { // drawing
        // Try all moves that preserve the draw.
        for (size_t i = 0; i < rootMoves.size(); ++i) {
            if (rootMoves[i].score == 0)
                rootMoves[j++] = rootMoves[i];
        }
    }

    rootMoves.resize(j, Search::RootMove(MOVE_NONE));

    return true;
}

// Use the WDL tables to filter out moves that don't preserve the win or draw.
// This is a fallback for the case that some or all DTZ tables are missing.
//
// A return value false indicates that not all probes were successful and that
// no moves were filtered out.
bool Tablebases::root_probe_wdl(Position& pos, Search::RootMoves& rootMoves, Value& score)
{
    ProbeState result;

    WDLScore wdl = Tablebases::probe_wdl(pos, &result);

    if (result == FAIL)
        return false;

    score = WDL_to_value[wdl + 2];

    StateInfo st;
    CheckInfo ci(pos);

    int best = WDLLoss;

    // Probe each move
    for (size_t i = 0; i < rootMoves.size(); ++i) {
        Move move = rootMoves[i].pv[0];
        pos.do_move(move, st, pos.gives_check(move, ci));
        WDLScore v = -Tablebases::probe_wdl(pos, &result);
        pos.undo_move(move);

        if (result == FAIL)
            return false;

        rootMoves[i].score = (Value)v;

        if (v > best)
            best = v;
    }

    size_t j = 0;

    for (size_t i = 0; i < rootMoves.size(); ++i) {
        if (rootMoves[i].score == best)
            rootMoves[j++] = rootMoves[i];
    }

    rootMoves.resize(j, Search::RootMove(MOVE_NONE));

    return true;
}
