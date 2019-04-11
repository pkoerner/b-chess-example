/*
  Title: A formal-based chess engine for ProB
  Author: Phillip Höfges
  Heinrich-Heine-Universität Düsseldorf
  Lehrstuhl für Softwaretechnik und Programmiersprachen
  Prof. Dr. Michael Leuschel, Sebastian Krings
*/

MACHINE chess
DEFINITIONS
  BWOFFSET(x,y) == (x+y) mod 2;
  ANIMATION_FUNCTION_DEFAULT == ( {r,c,i|r:1..8 & c:1..8 & i=(r+c) mod 2 }  );
  ANIMATION_FUNCTION1 == dom({r,c,i,Fig|Fig=black(c,9-r) & i = BlackImage(Fig)+BWOFFSET(c,r)}) ;
  ANIMATION_FUNCTION2 == dom({r,c,i,Fig|Fig=white(c,9-r) & i = WhiteImage(Fig)+BWOFFSET(c,r)}) ;
  BlackImage == {(b_king,2),(b_rook,4),(b_bishop,6),(b_knight,8),(b_pawn,10),(b_queen,12)};
  WhiteImage == {(w_king,14),(w_rook,16),(w_bishop,18),(w_knight,20),(w_pawn,22),(w_queen,24)};
  ANIMATION_IMG0 == "ChessPieces/empty_1.gif";
  ANIMATION_IMG1 == "ChessPieces/empty_2.gif";
  ANIMATION_IMG2 == "ChessPieces/b_king_1.gif"; // black king
  ANIMATION_IMG3 == "ChessPieces/b_king_2.gif";
  ANIMATION_IMG4 == "ChessPieces/b_rook_1.gif"; // black rook
  ANIMATION_IMG5 == "ChessPieces/b_rook_2.gif";
  ANIMATION_IMG6 == "ChessPieces/b_bishop_1.gif"; // black bishop
  ANIMATION_IMG7 == "ChessPieces/b_bishop_2.gif";
  ANIMATION_IMG8 == "ChessPieces/b_knight_1.gif"; // black knight
  ANIMATION_IMG9 == "ChessPieces/b_knight_2.gif";
  ANIMATION_IMG10 == "ChessPieces/b_pawn_1.gif"; // black pawn
  ANIMATION_IMG11 == "ChessPieces/b_pawn_2.gif";
  ANIMATION_IMG12 == "ChessPieces/b_queen_1.gif"; // black queen
  ANIMATION_IMG13 == "ChessPieces/b_queen_2.gif";
  ANIMATION_IMG14 == "ChessPieces/w_king_1.gif"; // white king
  ANIMATION_IMG15 == "ChessPieces/w_king_2.gif";
  ANIMATION_IMG16 == "ChessPieces/w_rook_1.gif"; // white rook
  ANIMATION_IMG17 == "ChessPieces/w_rook_2.gif";
  ANIMATION_IMG18 == "ChessPieces/w_bishop_1.gif"; // white bishop
  ANIMATION_IMG19 == "ChessPieces/w_bishop_2.gif";
  ANIMATION_IMG20 == "ChessPieces/w_knight_1.gif"; // white knight
  ANIMATION_IMG21 == "ChessPieces/w_knight_2.gif";
  ANIMATION_IMG22 == "ChessPieces/w_pawn_1.gif"; // white pawn
  ANIMATION_IMG23 == "ChessPieces/w_pawn_2.gif";
  ANIMATION_IMG24 == "ChessPieces/w_queen_1.gif"; // white queen
  ANIMATION_IMG25 == "ChessPieces/w_queen_2.gif";
  SET_PREF_MAX_OPERATIONS == 50;
INCLUDES board
PROMOTES
  white_promotion, black_promotion,
  white_castling, black_castling,
  move_white, move_black,
  white_en_passant, black_en_passant,
  evalState
END
