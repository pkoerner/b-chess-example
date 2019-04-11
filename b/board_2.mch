/*
  Title: A formal-based chess engine for ProB
  Author: Phillip Höfges
  Heinrich-Heine-Universität Düsseldorf
  Lehrstuhl für Softwaretechnik und Programmiersprachen
  Prof. Dr. Michael Leuschel, Sebastian Krings
*/

MACHINE board_2
SEES context_2
VARIABLES
  board, moving,
  castling_status, en_passant,
  fifty, value
INVARIANT
  board : (0..63) +-> FIGURES &
  moving : BOOL &
  castling_status : POW((COLORS*SIDES)*BOOL) &
  en_passant : {0} \/ 24..39 &
  fifty : 0..100 &
  value : INTEGER &
  card(board|>{w_king}) = 1 &
  card(board|>{w_queen}) : 0..9 &
  card(board|>{w_knight}) : 0..10 &
  card(board|>{w_rook}) : 0..10 &
  card(board|>{w_bishop}) : 0..10 &
  card(board|>{w_pawn}) : 0..8 &
  card(board|>{b_king}) = 1 &
  card(board|>{b_queen}) : 0..9 &
  card(board|>{b_knight}) : 0..10 &
  card(board|>{b_rook}) : 0..10 &
  card(board|>{b_bishop}) : 0..10 &
  card(board|>{b_pawn}) : 0..8
INITIALISATION
  board := {(0,w_rook),(1,w_knight),(2,w_bishop),(3,w_queen),
    (4,w_king),(5,w_bishop),(6,w_knight),(7,w_rook),(56,b_rook),(57,b_knight),
    (58,b_bishop),(59,b_queen),(60,b_king),(61,b_bishop),(62,b_knight),(63,b_rook)} \/
    {x,y | x : 8..15 & y = w_pawn} \/ {x,y | x : 48..55 & y = b_pawn};
  moving := TRUE;
  castling_status := (COLORS*SIDES)*{TRUE};
  en_passant := 0;
  fifty := 0;
  value := 0
DEFINITIONS
SET_PREF_MAX_OPERATIONS == 50;
// a field x is free
free(x, cur_board) == (
  x /: dom(cur_board)
);
// interval for vertical movement
ver_interval(x,y) == (
  IF x < y
  THEN {i | i : x+1..y & i mod 8 = y mod 8 & i < y}
  ELSE
    IF x > y
    THEN {i | i : y+1..x & i mod 8 = x mod 8 & i < x}
    ELSE {}
    END
  END
);
// interval for horizontal movement
hor_interval(x,y) == (
  IF x < y
  THEN x+1..y-1
  ELSE
    IF x > y
    THEN y+1..x-1
    ELSE {}
    END
  END
);
// move a black figure from x to y and take an opponent if take = 1
move_black_piece(figure, x, y, take, cur_board) == (
  (take = 0 => free(y, cur_board)) &
  (figure = b_king => move_king(x, y)) &
  (figure = b_queen => move_queen(x, y, cur_board)) &
  (figure = b_rook => move_rook(x, y, cur_board)) &
  (figure = b_knight => move_knight(x, y)) &
  (figure = b_bishop => move_bishop(x, y, cur_board)) &
  (figure = b_pawn => move_black_pawn(x, y, take, cur_board))
);
// move a white figure from x to y and take an opponent if take = 1
move_white_piece(figure, x, y, take, cur_board) == (
  (take = 0 => free(y, cur_board)) &
  (figure = w_king => move_king(x, y)) &
  (figure = w_queen => move_queen(x, y, cur_board)) &
  (figure = w_rook => move_rook(x, y, cur_board)) &
  (figure = w_knight => move_knight(x, y)) &
  (figure = w_bishop => move_bishop(x, y, cur_board)) &
  (figure = w_pawn => move_white_pawn(x, y, take, cur_board))
);
// move the white king form x to y and take an opponent if take = 1
// and opponent is not guarded
move_king(x, y) == (
  y : 0..63 &
  (x mod 8 = 0 => y : {x-8,x+1,x+7,x+8,x+9}) &
  (x mod 8 : 1..6 => y : {x-7,x-8,x-9,x-1,x+1,x+7,x+8,x+9}) &
  (x mod 8 = 7 => y : {x-8,x-9,x-1,x+7,x+8})
);
// move a queen from x to y
move_queen(x, y, cur_board) == (
  move_rook(x, y, cur_board) or
  move_bishop(x, y, cur_board)
);
// move a rook from x to y
move_rook(x, y, cur_board) == (
  y : 0..63 &
  IF y : {i | i : 0..63 & i mod 8 = x mod 8 & i /= x}
  THEN !(xx).(xx : ver_interval(x,y) => free(xx, cur_board))
  ELSE
    IF y : (x-(x mod 8)..x-(x mod 8)+7) - {x}
    THEN !(xx).(xx : hor_interval(x,y) => free(xx, cur_board))
    ELSE 1=0 END END
);
// move a knight from x to y
move_knight(x, y) == (
  y : 0..63 &
  (x mod 8 = 0 => y : {x-15,x-6,x+10,x+17}) & // a-file
  (x mod 8 = 1 => y : {x-17,x-15,x-6,x+10,x+15,x+17}) & // b-file
  (x mod 8 : 2..5 => y : {x-17,x-15,x-10,x-6,x+6,x+10,x+15,x+17}) &
  (x mod 8 = 6 => y : {x-17,x-15,x-10,x+6,x+15,x+17}) & // g-file
  (x mod 8 = 7 => y : {x-17,x-10,x+6,x+15}) // h-file
);
// move a bishop from x to y
move_bishop(x, y, cur_board) == (
  y : 0..63 &
  IF y : ran({i,j | i : 1..(x mod 8) & j = x+7*i})
  THEN
    !(xx).(xx : ran({i,j | i : 1..(x mod 8) & j = x+7*i}) & xx < y
      => free(xx, cur_board))
  ELSE
    IF y : ran({i,j | i : 1..(x mod 8) & j = x-9*i})
    THEN
      !(xx).(xx : ran({i,j | i : 1..(x mod 8) & j = x-9*i}) & xx > y
        => free(xx, cur_board))
    ELSE
      IF y : ran({i,j | i : 1..8-(x mod 8) & j = x+9*i})
      THEN
        !(xx).(xx : ran({i,j | i : 1..8-(x mod 8) & j = x+9*i}) & xx < y
          => free(xx, cur_board))
      ELSE
        IF y : ran({i,j | i : 1..8-(x mod 8) & j = x-7*i})
        THEN
          !(xx).(xx : ran({i,j | i : 1..8-(x mod 8) & j = x-7*i}) & xx > y
            => free(xx, cur_board))
        ELSE 1=0
        END
      END
    END
  END
);
// move a white pawn from x to y and respect its
// special taking behavior
move_white_pawn(x, y, take, cur_board) == (
  y : 16..55 &
  (take = 0 =>
    (x : 7..15 => y : {x+8,x+16} & free(x+8,cur_board)) &
    (x : 16..55 => y = x+8)) &
  (take = 1 =>
    (x mod 8 = 0 => y = x+9) &
    (x mod 8 : 1..6 => y : {x+7,x+9}) &
    (x mod 8 = 7 => y = x+7))
);
// move a black pawn from x to y and respect its
// special taking behavior
move_black_pawn(x, y, take, cur_board) == (
  y : 8..47 &
  (take = 0 =>
    (x : 48..55 => y : {x-8,x-16} & free(x-8,cur_board)) &
    (x : 7..47 => y = x-8)) &
  (take = 1 =>
    (x mod 8 = 0 => y = x-7) &
    (x mod 8 : 1..6 => y : {x-7,x-9}) &
    (x mod 8 = 7 => y = x-9))
);
// evaluation functions
special_pawns(n_board) == (
  // backward pawns (black)
  card({x | x : 0..55 & (x,b_pawn) : n_board & x : {y | #(i).(i = max({j | j : 8..55 & (j,b_pawn) : n_board}) &
      y >= i - (i mod 8) + 8 & y <= i - (i mod 8) + 8)}})
  // isolated pawns (white)
  + card({x | x : 0..55 & (x,b_pawn) : n_board & not(#(y).(y : 0..55 & ((y mod 8 = (x mod 8) + 1) or (y mod 8 = (x mod 8) - 1))))})
  // doubled pawns (white)
  + card({x | x : 0..55 & (x,b_pawn) : n_board & !(y).(y : 0..55 => y mod 8 = x mod 8)})
  // passed pawns (white)
  + card({x | x : 0..55 & (x,b_pawn) : n_board & not(#(y).(y : 0..x & (y mod 8 = (x mod 8) + 1 or y mod 8 = (x mod 8) - 1)))})
  // backward pawns (white)
  - card({x | x : 8..63 & (x,w_pawn) : n_board & x : {y | #(i).(i = min({j | j : 8..63 & (j,w_pawn) : n_board}) &
  y >= i - (i mod 8) + 8 & y <= i - (i mod 8) + 8)}})
  // isolated pawns (white)
  - card({x | x : 8..63 & (x,w_pawn) : n_board & not(#(y).(y : 8..63 & ((y mod 8 = (x mod 8) + 1) or (y mod 8 = (x mod 8) - 1))))})
  // doubled pawns (white)
  - card({x | x : 8..63 & (x,w_pawn) : n_board & !(y).(y : 8..63 => y mod 8 = x mod 8)})
  // passed pawns (white)
  - card({x | x : 8..63 & (x,w_pawn) : n_board & not(#(y).(y : 8..x & (y mod 8 = (x mod 8) + 1 or y mod 8 = (x mod 8) - 1)))})
);
// attack on adjacent king fields
adjacent_king_fields(n_board) == (
  card({x,figure | figure : BLACK_FIGURES & (x,figure) : n_board &
    #(k,y,take).((k,w_king) : n_board &
    y : 0..63 & y : {k-7,k-8,k-9,k-1,k+1,k+7,k+8,k+9} & take : {0,1} &
    move_black_piece(figure,x,y,take,n_board))}) -
  card({x,figure | (x,figure) : n_board &
    #(k,y,take).((k,b_king) : n_board &
    y : 0..63 & y : {k-7,k-8,k-9,k-1,k+1,k+7,k+8,k+9} & take : {0,1} &
    move_white_piece(figure,x,y,take,n_board))})
);
// check for semi open files
semi_open_files(n_board) == (
  card({file | file : 1..8 &
    (card({x | x : 1..8 & !(a).(a : 0..63 & (a,w_rook) : n_board =>
      move_rook(a,x*file,n_board))}) >= 5 or
     card({y | y : 1..8 & !(a).(a : 0..63 & (a,w_rook) : n_board =>
      move_rook(a*file,y,n_board))}) >= 5)}) -
  card({file | file : 1..8 &
    (card({x | x : 1..8 & !(a).(a : 0..63 & (a,b_rook) : n_board =>
      move_rook(a,x*file,n_board))}) >= 5 or
     card({y | y : 1..8 & !(a).(a : 0..63 & (a,b_rook) : n_board =>
      move_rook(a*file,y,n_board))}) >= 5)})
);
// pawns control center
control_center(n_board) == (
  card({(27,w_pawn),(28,w_pawn),(29,w_pawn),(35,w_pawn),(36,w_pawn),(37,w_pawn)} /\ n_board) - // ???
  card({(27,b_pawn),(28,b_pawn),(29,b_pawn),(35,b_pawn),(36,b_pawn),(37,b_pawn)} /\ n_board)
);
figures_to_values == (
  {(w_king,200),(w_queen,9),(w_knight,3),(w_bishop,3),(w_rook,5),(w_pawn,1),(b_king,-200),(b_queen,-9),(b_knight,-3),(b_bishop,-3),(b_rook,-5),(b_pawn,-1)}
);

// evaluate (factor for special_pawns and moves need to be find by tests)
evaluate == (
    SIGMA(z).(z : figures_to_values[ran(board)] | z) // all other figures
    + 1 * special_pawns(board) // # doubled, isolated and backward white pawns - # doubled, isolated and backward black pawns
    + 2 * semi_open_files(board) // # open files white - # open files black (at least 5 fields to move into one direction)
    + 2 * adjacent_king_fields(board) // attack on white - black kings adjacent fields
    + 3 * control_center(board) // difference between white and black pawn at center
)
OPERATIONS
  // execute a promition for a white pawn
  white_promotion(y, new_figure) =
    PRE
      card(board|>{w_king}) = 1 &
      fifty < 100 &
      moving = TRUE &
      new_figure : WHITE_FIGURES - {w_king, w_pawn}
    THEN
      ANY x, new_board
      WHERE
        x : 48..55 &
        (x,w_pawn) : board &
        (x = 48 => y : {56,57}) &
        (x : 49..54 => y : {x+7, x+8, x+9}) &
        (x = 55 => y : {62,63}) &
        new_board = (board <+ {(y,new_figure)}) - {(x,board(x))} &
        (y = x+8 => free(y, board)) &
        (y : {x+7, x+9} => y : dom(board) & board(y) : BLACK_FIGURES)
      THEN
        board := new_board ||
        moving := FALSE ||
        en_passant := 0 ||
        fifty := 0
      END // any
    END; // pre
  // execute a promition for a black pawn
  black_promotion(y, new_figure) =
    PRE
      card(board|>{b_king}) = 1 &
      fifty < 100 &
      moving = FALSE &
      new_figure : BLACK_FIGURES - {b_king, b_pawn}
    THEN
      ANY x, new_board
      WHERE
        x : 8..15 &
        (x,b_pawn) : board &
        (x = 8 => y : {0,1}) &
        (x : 9..14 => y : {x-7, x-8, x-9}) &
        (x = 15 => y : {6,7}) &
        new_board = (board <+ {(y,new_figure)})- {(x,board(x))} &
        (y = x-8 => free(y, board)) &
        (y : {x-7, x-9} => y : dom(board) & board(y) : WHITE_FIGURES)
      THEN
        board := new_board ||
        moving := TRUE ||
        en_passant := 0 ||
        fifty := 0
      END // any
    END; // pre
  // execute a white en_passant move
  white_en_passant =
    PRE
      card(board|>{w_king}) = 1 &
      fifty < 100 &
      moving = TRUE &
      en_passant /= 0
    THEN
      ANY a
      WHERE
        a : 32..39 /\ {en_passant-1,en_passant+1} &
        (a,w_pawn) : board
      THEN
        board := (board <+ {(en_passant+8,w_pawn)}) - {(en_passant,b_pawn),(a,w_pawn)} ||
        moving := FALSE ||
        en_passant := 0 ||
        fifty := 0
      END // any
    END; // pre
  // execute a black en_passant move
  black_en_passant =
    PRE
      card(board|>{b_king}) = 1 &
      fifty < 100 &
      moving = FALSE &
      en_passant /= 0
    THEN
      ANY a
      WHERE
        a : 24..31 /\ {en_passant-1,en_passant+1} &
        (a,b_pawn) : board
      THEN
        board := (board <+ {(en_passant-8,b_pawn)}) - {(en_passant,w_pawn),(a,b_pawn)} ||
        moving := TRUE ||
        en_passant := 0 ||
        fifty := 0
      END // any
    END; // pre
  // execute a white castling move to a given side
  white_castling(side) =
    PRE
      card(board|>{w_king}) = 1 &
      fifty < 100 &
      side : SIDES &
      moving = TRUE &
      #(k).((k,w_king) : board &
        card({y,f | f : BLACK_FIGURES & (y,f) : board &
          move_black_piece(f, y, k, 1, board)}) = 0)
    THEN
      ANY new_board
      WHERE
        castling_status(W,side) = TRUE &
        (4,w_king) : board &
        (side = kingside =>
          (7,w_rook) : board &
          !(i).(i : 5..6 => free(i,board) &
            card({j,fig | fig : BLACK_FIGURES & (j,fig) : board & move_black_piece(fig,j,i,0,board)}) = 0) &
          new_board = (board <+ {(6,w_king),(5,w_rook)}) - {(4,w_king),(7,w_rook)}) &
        (side = queenside =>
          (0,w_rook) : board &
          !(i).(i : 1..3 => free(i,board)) &
          !(i).(i : 2..3 =>
            card({j,fig | fig : BLACK_FIGURES & (j,fig) : board & move_black_piece(fig,j,i,0,board)}) = 0) &
          new_board = (board <+ {(2,w_king),(3,w_rook)}) -{(4,w_king),(0,w_rook)})
      THEN
        board := new_board ||
        moving := FALSE ||
        en_passant := 0 ||
        castling_status := castling_status <+ {((W,kingside),FALSE),((W,queenside),FALSE)} ||
        fifty := fifty + 1
      END // where
    END; // pre
  // execute a black castling move to a given side
  black_castling(side) =
    PRE
      card(board|>{b_king}) = 1 &
      fifty < 100 &
      side : SIDES &
      moving = FALSE &
      #(k).((k,b_king) : board &
        card({y,f | f : WHITE_FIGURES & (y,f) : board &
          move_white_piece(f, y, k, 1, board)}) = 0)
    THEN
      ANY new_board
      WHERE
        castling_status(B,side) = TRUE &
        (60,b_king) : board &
        (side = kingside =>
          (63,b_rook) : board &
          !(i).(i : 61..62 => free(i,board) &
            card({j,fig | fig : WHITE_FIGURES & (j,fig) : board & move_white_piece(fig,j,i,1,board)}) = 0) &
          new_board = (board <+ {(62,b_king),(61,b_rook)}) - {(60,b_king),(63,b_rook)}) &
        (side = queenside =>
          (56,b_rook) : board &
          !(i).(i : 57..59 => free(i,board)) &
          !(i).(i : 58..59 =>
            card({j,fig | fig : WHITE_FIGURES & (j,fig) : board & move_white_piece(fig,j,i,1,board)}) = 0) &
          new_board = (board <+ {(58,b_king),(59,b_rook)}) - {(60,b_king),(56,b_rook)})
      THEN
        board := new_board ||
        moving := TRUE ||
        en_passant := 0 ||
        castling_status := castling_status <+ {((B,kingside),FALSE),((B,queenside),FALSE)} ||
        fifty := fifty + 1
      END // where
    END; // pre
  // white figure on x move to y and eventually take an opponent figure
  move_white(figure, x, y, take) =
    ANY new_board
    WHERE
      card(board|>{w_king}) = 1 &
      fifty < 100 &
      figure : WHITE_FIGURES &
      figure : ran(board) &
      take : {0,1} &
      moving = TRUE &
      (x,figure) : board &
      (take = 1 => y : dom(board) & board(y) : BLACK_FIGURES) &
      new_board = (board <+ {(y,figure)}) - {(x,board(x))} &
      move_white_piece(figure, x, y, take, board)
    THEN
      moving := FALSE ||
      board := new_board ||
      IF (x : 0..15 & y : 24..31 & figure = w_pawn) THEN en_passant := y ELSE en_passant := 0 END ||
      IF figure = w_pawn or take = 1 THEN fifty := 0 ELSE fifty := fifty + 1 END ||
      IF figure = w_king THEN castling_status := castling_status <+ {((W,kingside),FALSE),((W,queenside),FALSE)} ELSE
        IF figure = w_rook & x = 7 THEN castling_status(W,kingside) := FALSE ELSE
          IF figure = w_rook & x = 0 THEN castling_status(W,queenside) := FALSE END END END
    END; // any
  // black figure on x move to y and eventually take an opponent figure
  move_black(figure, x, y, take) =
    ANY new_board
    WHERE
      card(board|>{b_king}) = 1 &
      fifty < 100 &
      figure : BLACK_FIGURES &
      figure : ran(board) &
      take : {0,1} &
      moving = FALSE &
      (x,figure) : board &
      (take = 1 => y : dom(board) & board(y) : WHITE_FIGURES) &
      new_board = (board <+ {(y,figure)}) - {(x,board(x))} &
      move_black_piece(figure, x, y, take, board)
    THEN
      moving := TRUE ||
      board := new_board ||
      IF (x : 48..55 & y : 32..39 & figure = b_pawn) THEN en_passant := y ELSE en_passant := 0 END ||
      IF figure = b_pawn or take = 1 THEN fifty := 0 ELSE fifty := fifty + 1 END ||
      IF figure = b_king THEN castling_status := castling_status <+ {((B,kingside),FALSE),((B,queenside),FALSE)} ELSE
        IF figure = b_rook & x = 63 THEN castling_status(B,kingside) := FALSE ELSE
          IF figure = b_rook & x = 58 THEN castling_status(B,queenside) := FALSE END END END
    END; // pre
  // eval
  evalState =
    BEGIN
      value := evaluate
    END;
  // tests
  test_promotion =
    BEGIN
      board := {(49,w_pawn),(15,w_king),(2,w_queen),(9,b_pawn),(55,b_king),(58,b_queen)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_en_passant =
    BEGIN
      board := {(36,w_pawn),(4,w_king),(51,b_pawn),(60,b_king)} ||
      moving := FALSE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_castling =
    BEGIN
      board := {(4,w_king),(7,w_rook),(60,b_king),(56,b_rook)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_checkmate =
    BEGIN
      board := {(4,w_king),(11,w_pawn),(12,w_pawn),(3,w_queen),
        (5,w_bishop),(60,b_king),(31,b_queen)} ||
      moving := FALSE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_checkmate_2 =
    BEGIN
      board := {(44,w_king),(52,w_queen),(60,b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_checkmate_3 =
    BEGIN
      board := {(15,w_king),(31,b_rook),(13,b_king)} ||
      moving := FALSE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_king_movement =
    BEGIN
      board := {(27,w_king),(60,b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_queen_movement =
    BEGIN
      board := {(27,w_queen),(4,w_king),(60,b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_rook_movement =
    BEGIN
      board := {(27,w_rook),(4,w_king),(60,b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_bishop_movement =
    BEGIN
      board := {(27,w_bishop),(4,w_king),(60,b_king)} ||
      moving := TRUE ||
      fifty := 0
    END;
  test_knight_movement =
    BEGIN
      board := {(27,w_knight),(4,w_king),(60,b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_pawn_movement =
    BEGIN
      board := {(27,w_pawn),(4,w_king),(60,b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_pin =
    BEGIN
      board := {(4,w_king),(39,w_queen),(60,b_king),(46,b_rook)} ||
      moving := FALSE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_fork =
    BEGIN
      board := {(4,w_king),(50,w_knight),(60,b_king),(56,b_rook)} ||
      moving := FALSE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_double_check =
    BEGIN
      board := {(4,w_king),(5,w_rook),(29,w_bishop),(61,b_king),(59,b_queen)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_movement_remis =
    BEGIN
      board := {(4,w_king),(7,b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 99
    END;
  test_remis =
    BEGIN
      board := {(7,w_king),(60,b_king),(22,b_queen)} ||
      moving := TRUE ||
      en_passant := 0 ||
      fifty := 0
    END;
  test_middlegame =
    BEGIN
      board := {(2,w_king),(3,w_rook),(6,w_rook),(9,w_pawn),
      (10,w_pawn),(11,w_pawn),(15,w_pawn),(27,w_bishop),
      (20,w_bishop),(21,w_pawn),(33,b_pawn),(35,w_queen),
      (36,b_pawn),(40,b_pawn),(43,b_pawn),(45,b_knight),
      (50,b_queen),(52,b_bishop),(53,w_pawn),(54,b_pawn),
      (55,b_pawn),(56,b_rook),(61,b_rook),(63,b_king)} ||
      moving := TRUE ||
      en_passant := 0 ||
      fifty := 0
    END
END
