/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2022 The Stockfish developers (see AUTHORS file)

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

#include <cassert>

#include "bitboard.h"
#include "movepick.h"

namespace Stockfish {

namespace {

  enum Stages {
    MAIN_TT, CAPTURE_INIT, GOOD_CAPTURE, REFUTATION, QUIET_INIT, QUIET, BAD_CAPTURE,
    EVASION_TT, EVASION_INIT, EVASION,
    PROBCUT_TT, PROBCUT_INIT, PROBCUT,
    QSEARCH_TT, QCAPTURE_INIT, QCAPTURE, QCHECK_INIT, QCHECK
  };

  // partial_insertion_sort() sorts moves in descending order up to and including
  // a given limit. The order of moves smaller than the limit is left unspecified.
  void partial_insertion_sort(ExtMove* begin, ExtMove* end, int limit) {

    for (ExtMove *sortedEnd = begin, *p = begin + 1; p < end; ++p)
        if (p->value >= limit)
        {
            ExtMove tmp = *p, *q;
            *p = *++sortedEnd;
            for (q = sortedEnd; q != begin && *(q - 1) < tmp; --q)
                *q = *(q - 1);
            *q = tmp;
        }
  }

} // namespace

auto f1 = [](int m){return Range(m-5000, m+5000);};
int ValA1 = 0, ValB1 = 0, ValC1 = 0, ValD1 = 0, ValE1 = 0, ValF1 = 0, ValG1 = 0, ValH1 = 0;
int ValA2 = 0, ValB2 = 0, ValC2 = 0, ValD2 = 0, ValE2 = 0, ValF2 = 0, ValG2 = 0, ValH2 = 0;
int ValA3 = 0, ValB3 = 0, ValC3 = 0, ValD3 = 0, ValE3 = 0, ValF3 = 0, ValG3 = 0, ValH3 = 0;
int ValA4 = 0, ValB4 = 0, ValC4 = 0, ValD4 = 0, ValE4 = 0, ValF4 = 0, ValG4 = 0, ValH4 = 0;
int ValA5 = 0, ValB5 = 0, ValC5 = 0, ValD5 = 0, ValE5 = 0, ValF5 = 0, ValG5 = 0, ValH5 = 0;
int ValA6 = 0, ValB6 = 0, ValC6 = 0, ValD6 = 0, ValE6 = 0, ValF6 = 0, ValG6 = 0, ValH6 = 0;
int ValA7 = 0, ValB7 = 0, ValC7 = 0, ValD7 = 0, ValE7 = 0, ValF7 = 0, ValG7 = 0, ValH7 = 0;
int ValA8 = 0, ValB8 = 0, ValC8 = 0, ValD8 = 0, ValE8 = 0, ValF8 = 0, ValG8 = 0, ValH8 = 0;
TUNE(SetRange(f1), ValA1 , ValB1 , ValC1 , ValD1 , ValE1 , ValF1 , ValG1 , ValH1);
TUNE(SetRange(f1), ValA2 , ValB2 , ValC2 , ValD2 , ValE2 , ValF2 , ValG2 , ValH2);
TUNE(SetRange(f1), ValA3 , ValB3 , ValC3 , ValD3 , ValE3 , ValF3 , ValG3 , ValH3);
TUNE(SetRange(f1), ValA4 , ValB4 , ValC4 , ValD4 , ValE4 , ValF4 , ValG4 , ValH4);
TUNE(SetRange(f1), ValA5 , ValB5 , ValC5 , ValD5 , ValE5 , ValF5 , ValG5 , ValH5);
TUNE(SetRange(f1), ValA6 , ValB6 , ValC6 , ValD6 , ValE6 , ValF6 , ValG6 , ValH6);
TUNE(SetRange(f1), ValA7 , ValB7 , ValC7 , ValD7 , ValE7 , ValF7 , ValG7 , ValH7);
TUNE(SetRange(f1), ValA8 , ValB8 , ValC8 , ValD8 , ValE8 , ValF8 , ValG8 , ValH8);

int knightPsq[SQUARE_NB] = 
{
    ValA1 , ValB1 , ValC1 , ValD1 , ValE1 , ValF1 , ValG1 , ValH1,
    ValA2 , ValB2 , ValC2 , ValD2 , ValE2 , ValF2 , ValG2 , ValH2,
    ValA3 , ValB3 , ValC3 , ValD3 , ValE3 , ValF3 , ValG3 , ValH3,
    ValA4 , ValB4 , ValC4 , ValD4 , ValE4 , ValF4 , ValG4 , ValH4,
    ValA5 , ValB5 , ValC5 , ValD5 , ValE5 , ValF5 , ValG5 , ValH5,
    ValA6 , ValB6 , ValC6 , ValD6 , ValE6 , ValF6 , ValG6 , ValH6,
    ValA7 , ValB7 , ValC7 , ValD7 , ValE7 , ValF7 , ValG7 , ValH7,
    ValA8 , ValB8 , ValC8 , ValD8 , ValE8 , ValF8 , ValG8 , ValH8
};


/// Constructors of the MovePicker class. As arguments we pass information
/// to help it to return the (presumably) good moves first, to decide which
/// moves to return (in the quiescence search, for instance, we only want to
/// search captures, promotions, and some checks) and how important good move
/// ordering is at the current node.

/// MovePicker constructor for the main search
MovePicker::MovePicker(const Position& p, Move ttm, Depth d, const ButterflyHistory* mh,
                                                             const CapturePieceToHistory* cph,
                                                             const PieceToHistory** ch,
                                                             Move cm,
                                                             const Move* killers)
           : pos(p), mainHistory(mh), captureHistory(cph), continuationHistory(ch),
             ttMove(ttm), refutations{{killers[0], 0}, {killers[1], 0}, {cm, 0}}, depth(d)
{
  assert(d > 0);

  stage = (pos.checkers() ? EVASION_TT : MAIN_TT) +
          !(ttm && pos.pseudo_legal(ttm));
}

/// MovePicker constructor for quiescence search
MovePicker::MovePicker(const Position& p, Move ttm, Depth d, const ButterflyHistory* mh,
                                                             const CapturePieceToHistory* cph,
                                                             const PieceToHistory** ch,
                                                             Square rs)
           : pos(p), mainHistory(mh), captureHistory(cph), continuationHistory(ch), ttMove(ttm), recaptureSquare(rs), depth(d)
{
  assert(d <= 0);

  stage = (pos.checkers() ? EVASION_TT : QSEARCH_TT) +
          !(   ttm
            && (pos.checkers() || depth > DEPTH_QS_RECAPTURES || to_sq(ttm) == recaptureSquare)
            && pos.pseudo_legal(ttm));
}

/// MovePicker constructor for ProbCut: we generate captures with SEE greater
/// than or equal to the given threshold.
MovePicker::MovePicker(const Position& p, Move ttm, Value th, Depth d, const CapturePieceToHistory* cph)
           : pos(p), captureHistory(cph), ttMove(ttm), threshold(th), depth(d)
{
  assert(!pos.checkers());

  stage = PROBCUT_TT + !(ttm && pos.capture(ttm)
                             && pos.pseudo_legal(ttm)
                             && pos.see_ge(ttm, threshold));
}

/// MovePicker::score() assigns a numerical value to each move in a list, used
/// for sorting. Captures are ordered by Most Valuable Victim (MVV), preferring
/// captures with a good history. Quiets moves are ordered using the histories.
template<GenType Type>
void MovePicker::score() {

  static_assert(Type == CAPTURES || Type == QUIETS || Type == EVASIONS, "Wrong type");

  Bitboard threatened, threatenedByPawn, threatenedByMinor, threatenedByRook;
  if constexpr (Type == QUIETS)
  {
      Color us = pos.side_to_move();
      // squares threatened by pawns
      threatenedByPawn  = pos.attacks_by<PAWN>(~us);
      // squares threatened by minors or pawns
      threatenedByMinor = pos.attacks_by<KNIGHT>(~us) | pos.attacks_by<BISHOP>(~us) | threatenedByPawn;
      // squares threatened by rooks, minors or pawns
      threatenedByRook  = pos.attacks_by<ROOK>(~us) | threatenedByMinor;

      // pieces threatened by pieces of lesser material value
      threatened =  (pos.pieces(us, QUEEN) & threatenedByRook)
                  | (pos.pieces(us, ROOK)  & threatenedByMinor)
                  | (pos.pieces(us, KNIGHT, BISHOP) & threatenedByPawn);
  }
  else
  {
      // Silence unused variable warnings
      (void) threatened;
      (void) threatenedByPawn;
      (void) threatenedByMinor;
      (void) threatenedByRook;
  }

  for (auto& m : *this)
      if constexpr (Type == CAPTURES)
          m.value =  6 * int(PieceValue[MG][pos.piece_on(to_sq(m))])
                   +     (*captureHistory)[pos.moved_piece(m)][to_sq(m)][type_of(pos.piece_on(to_sq(m)))];

      else if constexpr (Type == QUIETS)
          m.value =      (*mainHistory)[pos.side_to_move()][from_to(m)]
                   + 2 * (*continuationHistory[0])[pos.moved_piece(m)][to_sq(m)]
                   +     (*continuationHistory[1])[pos.moved_piece(m)][to_sq(m)]
                   +     (*continuationHistory[3])[pos.moved_piece(m)][to_sq(m)]
                   +     (*continuationHistory[5])[pos.moved_piece(m)][to_sq(m)]
                   +     (threatened & from_sq(m) ?
                           (type_of(pos.moved_piece(m)) == QUEEN && !(to_sq(m) & threatenedByRook)  ? 50000
                          : type_of(pos.moved_piece(m)) == ROOK  && !(to_sq(m) & threatenedByMinor) ? 25000
                          :                                         !(to_sq(m) & threatenedByPawn)  ? 15000
                          :                                                                           0)
                          :                                                                           0)
                   +    (type_of(pos.moved_piece(m)) == KNIGHT ? knightPsq[relative_square(pos.side_to_move(), to_sq(m))] 
                                                               - knightPsq[relative_square(pos.side_to_move(), from_sq(m))] : 0);
      else // Type == EVASIONS
      {
          if (pos.capture(m))
              m.value =  PieceValue[MG][pos.piece_on(to_sq(m))]
                       - Value(type_of(pos.moved_piece(m)));
          else
              m.value =      (*mainHistory)[pos.side_to_move()][from_to(m)]
                       + 2 * (*continuationHistory[0])[pos.moved_piece(m)][to_sq(m)]
                       - (1 << 28);
      }
}

/// MovePicker::select() returns the next move satisfying a predicate function.
/// It never returns the TT move.
template<MovePicker::PickType T, typename Pred>
Move MovePicker::select(Pred filter) {

  while (cur < endMoves)
  {
      if (T == Best)
          std::swap(*cur, *std::max_element(cur, endMoves));

      if (*cur != ttMove && filter())
          return *cur++;

      cur++;
  }
  return MOVE_NONE;
}

/// MovePicker::next_move() is the most important method of the MovePicker class. It
/// returns a new pseudo-legal move every time it is called until there are no more
/// moves left, picking the move with the highest score from a list of generated moves.
Move MovePicker::next_move(bool skipQuiets) {

top:
  switch (stage) {

  case MAIN_TT:
  case EVASION_TT:
  case QSEARCH_TT:
  case PROBCUT_TT:
      ++stage;
      return ttMove;

  case CAPTURE_INIT:
  case PROBCUT_INIT:
  case QCAPTURE_INIT:
      cur = endBadCaptures = moves;
      endMoves = generate<CAPTURES>(pos, cur);

      score<CAPTURES>();
      partial_insertion_sort(cur, endMoves, -3000 * depth);
      ++stage;
      goto top;

  case GOOD_CAPTURE:
      if (select<Next>([&](){
                       return pos.see_ge(*cur, Value(-69 * cur->value / 1024)) ?
                              // Move losing capture to endBadCaptures to be tried later
                              true : (*endBadCaptures++ = *cur, false); }))
          return *(cur - 1);

      // Prepare the pointers to loop over the refutations array
      cur = std::begin(refutations);
      endMoves = std::end(refutations);

      // If the countermove is the same as a killer, skip it
      if (   refutations[0].move == refutations[2].move
          || refutations[1].move == refutations[2].move)
          --endMoves;

      ++stage;
      [[fallthrough]];

  case REFUTATION:
      if (select<Next>([&](){ return    *cur != MOVE_NONE
                                    && !pos.capture(*cur)
                                    &&  pos.pseudo_legal(*cur); }))
          return *(cur - 1);
      ++stage;
      [[fallthrough]];

  case QUIET_INIT:
      if (!skipQuiets)
      {
          cur = endBadCaptures;
          endMoves = generate<QUIETS>(pos, cur);

          score<QUIETS>();
          partial_insertion_sort(cur, endMoves, -3000 * depth);
      }

      ++stage;
      [[fallthrough]];

  case QUIET:
      if (   !skipQuiets
          && select<Next>([&](){return   *cur != refutations[0].move
                                      && *cur != refutations[1].move
                                      && *cur != refutations[2].move;}))
          return *(cur - 1);

      // Prepare the pointers to loop over the bad captures
      cur = moves;
      endMoves = endBadCaptures;

      ++stage;
      [[fallthrough]];

  case BAD_CAPTURE:
      return select<Next>([](){ return true; });

  case EVASION_INIT:
      cur = moves;
      endMoves = generate<EVASIONS>(pos, cur);

      score<EVASIONS>();
      ++stage;
      [[fallthrough]];

  case EVASION:
      return select<Best>([](){ return true; });

  case PROBCUT:
      return select<Next>([&](){ return pos.see_ge(*cur, threshold); });

  case QCAPTURE:
      if (select<Next>([&](){ return   depth > DEPTH_QS_RECAPTURES
                                    || to_sq(*cur) == recaptureSquare; }))
          return *(cur - 1);

      // If we did not find any move and we do not try checks, we have finished
      if (depth != DEPTH_QS_CHECKS)
          return MOVE_NONE;

      ++stage;
      [[fallthrough]];

  case QCHECK_INIT:
      cur = moves;
      endMoves = generate<QUIET_CHECKS>(pos, cur);

      ++stage;
      [[fallthrough]];

  case QCHECK:
      return select<Next>([](){ return true; });
  }

  assert(false);
  return MOVE_NONE; // Silence warning
}

} // namespace Stockfish
