/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2008 Tord Romstad (Glaurung author)
  Copyright (C) 2008-2015 Marco Costalba, Joona Kiiski, Tord Romstad
  Copyright (C) 2015-2019 Marco Costalba, Joona Kiiski, Gary Linscott, Tord Romstad

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

#include "types.h"

Value PieceValue[PHASE_NB][PIECE_NB] = {
  { VALUE_ZERO, PawnValueMg, KnightValueMg, BishopValueMg, RookValueMg, QueenValueMg },
  { VALUE_ZERO, PawnValueEg, KnightValueEg, BishopValueEg, RookValueEg, QueenValueEg }
};

namespace PSQT {

#define S(mg, eg) make_score(mg, eg)

// Bonus[PieceType][Square / 2] contains Piece-Square scores. For each piece
// type on a given square a (middlegame, endgame) score pair is assigned. Table
// is defined for files A..D and white side: it is symmetric for black side and
// second half of the files.
constexpr Score Bonus[][RANK_NB][int(FILE_NB) / 2] = {
  { },
  { // Pawn
   { S(  0, 0), S(  0,  0), S(  0, 0), S( 0, 0) },
   { S(-11,-3), S(  7, -1), S(  7, 7), S(17, 2) },
   { S(-16,-2), S( -3,  2), S( 23, 6), S(23,-1) },
   { S(-14, 7), S( -7, -4), S( 20,-8), S(24, 2) },
   { S( -5,13), S( -2, 10), S( -1,-1), S(12,-8) },
   { S(-11,16), S(-12,  6), S( -2, 1), S( 4,16) },
   { S( -2, 1), S( 20,-12), S(-10, 6), S(-2,25) }
  },
  { // Knight
   { S(-169,-105), S(-96,-74), S(-80,-46), S(-79,-18) },
   { S( -79, -70), S(-39,-56), S(-24,-15), S( -9,  6) },
   { S( -64, -38), S(-20,-33), S(  4, -5), S( 19, 27) },
   { S( -28, -36), S(  5,  0), S( 41, 13), S( 47, 34) },
   { S( -29, -41), S( 13,-20), S( 42,  4), S( 52, 35) },
   { S( -11, -51), S( 28,-38), S( 63,-17), S( 55, 19) },
   { S( -67, -64), S(-21,-45), S(  6,-37), S( 37, 16) },
   { S(-200, -98), S(-80,-89), S(-53,-53), S(-32,-16) }
  },
  { // Bishop
   { S(-46,-61), S( -5,-30), S(-11,-36), S(-31, -13) },
   { S(-21,-36), S(  8,-11), S( 14,-14), S(  2,  2) },
   { S( -8,-20), S( 23,  0), S( -3, -5), S( 14, 14) },
   { S(  2,-26), S(  8, -3), S( 22, -2), S( 38, 16) },
   { S( -7,-25), S( 29, -5), S( 18,-9), S( 29, 15) },
   { S(-17,-25), S(  9,  0), S( -3,  1), S(  7, 15) },
   { S(-20,-34), S(-16,-14), S( 8, -9), S( -8,  8) },
   { S(-48,-53), S( -5,-36), S(-14,-38), S(-27,-19) }
  },
  { // Rook
   { S(-24, -1), S(-14,-2), S( -7, -2), S( 1,0) },
   { S(-18,-9), S(-8,-6), S( -3, -2), S( 5, 0) },
   { S(-20, 8), S( -8,-5), S(  2,  2), S(-1,0) },
   { S(-17, -3), S( -6, 3), S( -4, -5), S(-5, 5) },
   { S(-23, -8), S(-12, 5), S( -1,  0), S( 5,-8) },
   { S(-24,  3), S( -7,-2), S(  3,-6), S(8, 5) },
   { S( -9,  1), S(  7, 4), S( 10, 14), S(12,-5) },
   { S(-23, 9), S(-21,-1), S( -8, 10), S( 3, 5) }
  },
  { // Queen
   { S(  3,-69), S(-5,-57), S(-5,-47), S( 4,-26) },
   { S( -3,-55), S( 5,-31), S( 8,-22), S(12, -4) },
   { S( -3,-39), S( 6,-18), S(13, -9), S( 7,  3) },
   { S(  4,-23), S( 5, -3), S( 9, 13), S( 8, 24) },
   { S(  0,-29), S(14, -6), S(12,  9), S( 5, 21) },
   { S( -4,-38), S(10,-18), S( 6,-12), S( 8,  1) },
   { S( -5,-50), S( 6,-27), S(10,-24), S( 8, -8) },
   { S( -2,-75), S(-2,-52), S( 1,-43), S(-2,-36) }
  },
  { // King
   { S(272,  0), S(325, 41), S(273, 80), S(190, 93) },
   { S(277, 57), S(305, 98), S(241,138), S(183,131) },
   { S(198, 86), S(253,138), S(168,165), S(120,173) },
   { S(169,103), S(191,152), S(136,168), S(108,169) },
   { S(145, 98), S(176,166), S(112,197), S(69, 194) },
   { S(122, 87), S(159,164), S(85, 174), S(36, 189) },
   { S(87,  40), S(120, 99), S(64, 128), S(25, 141) },
   { S(64,   5), S(87,  60), S(49,  75), S(0,   75) }
  }
};

#undef S

Score psq[PIECE_NB][SQUARE_NB];

// init() initializes piece-square tables: the white halves of the tables are
// copied from Bonus[] adding the piece value, then the black halves of the
// tables are initialized by flipping and changing the sign of the white scores.
void init() {

  for (Piece pc = W_PAWN; pc <= W_KING; ++pc)
  {
      PieceValue[MG][~pc] = PieceValue[MG][pc];
      PieceValue[EG][~pc] = PieceValue[EG][pc];

      Score score = make_score(PieceValue[MG][pc], PieceValue[EG][pc]);

      for (Square s = SQ_A1; s <= SQ_H8; ++s)
      {
          File f = std::min(file_of(s), ~file_of(s));
          psq[ pc][ s] = score + Bonus[pc][rank_of(s)][f];
          psq[~pc][~s] = -psq[pc][s];
      }
  }
}

} // namespace PSQT
