/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2021 The Stockfish developers (see AUTHORS file)

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


#include "psqt.h"

#include <algorithm>

#include "bitboard.h"
#include "types.h"

namespace Stockfish {

namespace
{

auto constexpr S = make_score;

// 'Bonus' contains Piece-Square parameters.
// Scores are explicit for files A to D, implicitly mirrored for E to H.
constexpr Score Bonus[][RANK_NB][int(FILE_NB) / 2] = {
  { },
  { },
  { // Knight
   { S(0,-60), S(0, -30),  S(0, 0) }   
  },
  { // Bishop
   { S(0,-100), S(0, -50),  S(0, 0) }   
  },
  { // Rook
   { S(0,-90), S(0, -45),  S(0,  0) }
  },
  { // Queen
   { S(0,-150), S(0, -75),  S(0,  0) }
  },
  { // King
   { S(0,  0), S(0, -5), S(0, -10) }
     }
};

constexpr Score PBonus[RANK_NB][FILE_NB] =
  { // Pawn (asymmetric distribution)
   { },
   { S(0, 0), S(0, 1),  S( 0, 2) }
  };

} // namespace


namespace PSQT
{

Score psq[PIECE_NB][SQUARE_NB];

// PSQT::init() initializes piece-square tables: the white halves of the tables are
// copied from Bonus[] and PBonus[], adding the piece value, then the black halves of
// the tables are initialized by flipping and changing the sign of the white scores.
void init() {

  for (Piece pc : {W_PAWN, W_KNIGHT, W_BISHOP, W_ROOK, W_QUEEN, W_KING})
  {
    Score score = make_score(PieceValue[MG][pc], PieceValue[EG][pc]);

    for (Square s = SQ_A1; s <= SQ_H8; ++s)
    {
      File f = File(edge_distance(file_of(s)));
      psq[ pc][s] = score + (type_of(pc) == PAWN ? PBonus[rank_of(s)][file_of(s)]
                                                 : Bonus[pc][rank_of(s)][f]);
      psq[~pc][flip_rank(s)] = -psq[pc][s];
    }
  }
}

} // namespace PSQT

} // namespace Stockfish
