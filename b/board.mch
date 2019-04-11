/*
  Title: A formal-based chess engine for ProB
  Author: Phillip Höfges
  Heinrich-Heine-Universität Düsseldorf
  Lehrstuhl für Softwaretechnik und Programmiersprachen
  Prof. Dr. Michael Leuschel, Sebastian Krings
*/

MACHINE board
SEES context
VARIABLES
  white, black, moving,
  in_check,
  castling_status, en_passant,
  fifty, value
INVARIANT
  white : ((1..8)*(1..8)) +-> WHITE_FIGURES &
  black : ((1..8)*(1..8)) +-> BLACK_FIGURES &
  moving : BOOL &
  in_check : BOOL &
  castling_status : POW((COLORS*SIDES)*BOOL) &
  en_passant : 0..8 &
  fifty : 0..100 &
  value : INTEGER &
  card(white|>{w_king}) = 1 &
  card(white|>{w_queen}) : 0..9 &
  card(white|>{w_knight}) : 0..10 &
  card(white|>{w_rook}) : 0..10 &
  card(white|>{w_bishop}) : 0..10 &
  card(white|>{w_pawn}) : 0..8 &
  card(black|>{b_king}) = 1 &
  card(black|>{b_queen}) : 0..9 &
  card(black|>{b_knight}) : 0..10 &
  card(black|>{b_rook}) : 0..10 &
  card(black|>{b_bishop}) : 0..10 &
  card(black|>{b_pawn}) : 0..8
INITIALISATION
  white := {((1,1),w_rook), ((2,1),w_knight), ((3,1),w_bishop), ((4,1),w_queen),
    ((5,1),w_king), ((6,1),w_bishop), ((7,1),w_knight), ((8,1),w_rook), ((1,2),w_pawn),
    ((2,2),w_pawn), ((3,2),w_pawn), ((4,2),w_pawn), ((5,2),w_pawn), ((6,2),w_pawn),
    ((7,2),w_pawn), ((8,2),w_pawn)};
  black := {((1,8),b_rook), ((2,8),b_knight), ((3,8),b_bishop), ((4,8),b_queen),
    ((5,8),b_king), ((6,8),b_bishop), ((7,8),b_knight), ((8,8),b_rook), ((1,7),b_pawn),
    ((2,7),b_pawn), ((3,7),b_pawn), ((4,7),b_pawn), ((5,7),b_pawn), ((6,7),b_pawn),
    ((7,7),b_pawn), ((8,7),b_pawn)};
  moving := TRUE;
  in_check := FALSE;
  castling_status := (COLORS*SIDES)*{TRUE};
  en_passant := 0;
  fifty := 0;
  value := 0
DEFINITIONS
SET_PREF_MAX_OPERATIONS == 50;
// a field (x,y) is free
free(x, y, cur_white, cur_black) == (
  (x,y) /: dom(cur_white) &
  (x,y) /: dom(cur_black)
);
// find the interval to check for other figures in the way
in_order_interval(ret,delta,ab,xy) == (
  (ab<xy => ret : (ab+1)..(xy-1) & delta = ret-ab) &
  (ab>xy => ret : (xy+1)..(ab-1) & delta = ret-xy) &
  (ab=xy => ret : {} & delta = 0)
);
// move a black figure from (a,b) to (x,y) and take an opponent if take = 1
move_black_piece(figure, a, b, x, y, take, cur_white, cur_black) == (
  (take = 0 => free(x, y, cur_white, cur_black)) &
  (figure = b_king => move_king(a, b, x, y)) &
  (figure = b_queen => move_queen(a, b, x, y, cur_white, cur_black)) &
  (figure = b_rook => move_rook(a, b, x, y, cur_white, cur_black)) &
  (figure = b_knight => move_knight(a, b, x, y)) &
  (figure = b_bishop => move_bishop(a, b, x, y, cur_white, cur_black)) &
  (figure = b_pawn => move_black_pawn(a, b, x, y, take, cur_white, cur_black))
);
// move a white figure from (a,b) to (x,y) and take an opponent if take = 1
move_white_piece(figure, a, b, x, y, take, cur_white, cur_black) == (
   (take = 0 => free(x, y, cur_white, cur_black)) &
   (figure = w_king => move_king(a, b, x, y)) &
   (figure = w_queen => move_queen(a, b, x, y, cur_white, cur_black)) &
   (figure = w_rook => move_rook(a, b, x, y, cur_white, cur_black)) &
   (figure = w_knight => move_knight(a, b, x, y)) &
   (figure = w_bishop => move_bishop(a, b, x, y, cur_white, cur_black)) &
   (figure = w_pawn => move_white_pawn(a, b, x, y, take, cur_white, cur_black))
);
// move the white king form (a,b) to (x,y) and take an opponent if take = 1
// and opponent is not guarded
move_king(a, b, x, y) == (
    x : {a-1,a,a+1} & x : 1..8 &
    y : {b-1,b,b+1} & y : 1..8
);
// move a queen from (a,b) to (x,y)
move_queen(a, b, x, y, cur_white, cur_black) == (
  move_rook(a, b, x, y, cur_white, cur_black) or
  move_bishop(a, b, x, y, cur_white, cur_black)
);
// move a rook from (a,b) to (x,y)
move_rook(a, b, x, y, cur_white, cur_black) == (
  x : 1..8 & y : 1..8 &
  ((a=x & !yy.(yy : b+1..y-1 => free(x,yy,cur_white,cur_black))
    & !yy.(yy : y+1..b-1 => free(x,yy,cur_white,cur_black)))
  or
  (b=y & !xx.(xx : a+1..x-1 => free(xx,y,cur_white,cur_black))
    & !xx.(xx : x+1..a-1 => free(xx,y,cur_white,cur_black))))
);
// move a knight from (a,b) to (x,y)
move_knight(a, b, x, y) == (
    x : 1..8 & x : {a-1, a-2, a+1, a+2} &
    y : 1..8 & y : {b-1, b-2, b+1, b+2} &
    (x : {a-1,a+1} <=> y /: {b-1,b+1})
);
// move a bishop from (a,b) to (x,y)
move_bishop(a, b, x, y, cur_white, cur_black) == (
  x : 1..8 & y : 1..8 & a /= x & b /= y &
  (a-x) : {(b-y), (y-b)} &
  !(xx,yy,deltax,deltay,abs).(
    (abs : {(x-a), (a-x)} & abs > 0 &
    in_order_interval(xx,deltax,a,x) &
    in_order_interval(yy,deltay,b,y)) =>
      ((((x>a & y>b) or (x<a & y<b)) & deltax = deltay) => free(xx,yy,cur_white,cur_black)) &
      ((((x>a & y<b) or (x<a & y>b)) & deltax + deltay = abs) => free(xx,yy,cur_white,cur_black)))
);
// move a white pawn from (a,b) to (x,y) and respect its
// special taking behavior
move_white_pawn(a, b, x, y, take, cur_white, cur_black) == (
  (take = 0 =>
    x = a &
    (b = 2 => y : {3,4} & free(x,3,cur_white,cur_black)) &
    (b > 2 => y = b+1)) &
  (take = 1 =>
    y = b + 1 &
    x : {a+1, a-1})
);
// move a black pawn from (a,b) to (x,y) and respect its
// special taking behavior
move_black_pawn(a, b, x, y, take, cur_white, cur_black) == (
  (take = 0 =>
    x = a &
    (b = 7 => y : {5,6} & free(x,6,cur_white,cur_black)) &
    (b < 7 => y = b-1)) &
  (take = 1 =>
    y = b - 1 &
    x : {a+1, a-1})
);
// check if white is not in check given the next board
not_in_check_white(cur_white, cur_black) == (
  #(kx,ky).( ((kx,ky),w_king) : cur_white & /* there should always be one position */
    !(i,j,figureb).(
      ((i,j),figureb) : cur_black =>
        not(move_black_piece(figureb, i, j, kx, ky, 1, cur_white, cur_black))))
);
// check if black is not in check given the next board
not_in_check_black(cur_white, cur_black) == (
  #(kx,ky).( ((kx,ky),b_king) : cur_black & /* there should always be one position */
    !(i,j,figurew).(
      ((i,j),figurew) : cur_white =>
        not(move_white_piece(figurew, i, j, kx, ky, 1, cur_white, cur_black))))
);
// evaluation functions
"LibraryMeta.def";
Operations == card({i | i : INTEGER & STATE_SUCC(CURRENT_STATE_ID,i)});
kings == (
  IF (Operations = 0 & in_check = TRUE) THEN
    (IF moving = TRUE THEN 1 ELSE -1 END) ELSE 0 END
);
special_pawns(n_white, n_black) == (
  // backward pawns (white)
    card({x,y | x : 1..8 & y : 1..8 & ((x,y),w_pawn) : n_white & y = min({j | j : 1..8 & #(i).(i : 1..8 & ((i,j),w_pawn) : n_white)})})
  // isolated pawns (white)
  + card({x,y | x : 1..8 & y : 1..8 & ((x,y),w_pawn) : n_white & not(#(i,j).(i : 1..8 & j : 1..8 & i : {y-1, y+1} & ((i,j),w_pawn) : n_white))})
  // doubled pawns (white)
  + card({x,y | x : 1..8 & y : 1..8 & ((x,y),w_pawn) : n_white & #(i).(i : (1..8) - {y} & ((i,x),w_pawn) : n_white)})
  // passed pawns (white)
  + card({x,y | x : 1..8 & y : 1..8 & ((x,y),w_pawn) : n_white & not(#(i,j).(i : 1..8 & j : y..8 & i : {x-1, x, x+1}))})
  // backward pawns (black)
  - card({x,y | x : 1..8 & y : 1..8 & ((x,y),b_pawn) : n_black & y = max({j | j : 1..8 & #(i).(i : 1..8 & ((i,j),b_pawn) : n_black)})})
  // isolated pawns (black)
  - card({x,y | x : 1..8 & y : 1..8 & ((x,y),b_pawn) : n_black & not(#(i,j).(i : 1..8 & j : 1..8 & i : {y-1, y+1} & ((i,j),b_pawn) : n_black))})
  // doubled pawns (black)
  - card({x,y | x : 1..8 & y : 1..8 & ((x,y),b_pawn) : n_black & #(i).(i : (1..8) - {y} & ((i,x),b_pawn) : n_black)})
  // passed pawns (black)
  - card({x,y | x : 1..8 & y : 1..8 & ((x,y),b_pawn) : n_black & not(#(i,j).(i : 1..8 & j : 1..y & i : {x-1, x, x+1}))})
);
// attack on adjacent king fields
adjacent_king_fields(n_white, n_black) == (
  card({a,b,figure | (a,b,figure) : n_black &
    #(i,j,x,y,take).(((i,j),w_king) : n_white &
    x : 1..8 & y : 1..8 & x : {i-1,i,i+1} & y : {j-1,j,j+1} & take : {0,1} & (x,y) /= (i,j) &
    move_black_piece(figure,a,b,x,y,take,n_white,n_black))}) -
  card({a,b,figure | (a,b,figure) : n_white &
    #(i,j,x,y,take).(((i,j),b_king) : n_black &
    x : 1..8 & y : 1..8 & x : {i-1,i,i+1} & y : {j-1,j,j+1} & take : {0,1} & (x,y) /= (i,j) &
    move_white_piece(figure,a,b,x,y,take,n_white,n_black))})
);
// check for semi open files
semi_open_files(n_white, n_black) == (
  card({file | file : 1..8 &
    (card({x | x : 1..8 & !(a,b).(a : 1..8 & b : 1..8 & ((a,b),w_rook) : n_white =>
      move_rook(a,b,x,file,n_white,n_black))}) >= 5 or
     card({y | y : 1..8 & !(a,b).(a : 1..8 & b : 1..8 & ((a,b),w_rook) : n_white =>
      move_rook(a,b,file,y,n_white,n_black))}) >= 5)}) -
  card({file | file : 1..8 &
    (card({x | x : 1..8 & !(a,b).(a : 1..8 & b : 1..8 & ((a,b),b_rook) : n_black =>
      move_rook(a,b,x,file,n_white,n_black))}) >= 5 or
     card({y | y : 1..8 & !(a,b).(a : 1..8 & b : 1..8 & ((a,b),b_rook) : n_black =>
      move_rook(a,b,file,y,n_white,n_black))}) >= 5)})
);
// pawns control center
control_center(n_white, n_black) == (
  card({(4,4,w_pawn),(5,4,w_pawn),(6,4,w_pawn),(4,5,w_pawn),(5,5,w_pawn),(6,5,w_pawn)} /\ n_white) - // ???
  card({(4,4,b_pawn),(5,4,b_pawn),(6,4,b_pawn),(4,5,b_pawn),(5,5,b_pawn),(6,5,b_pawn)} /\ n_black)
);
figures_to_values == (
  {(w_king,0),(w_queen,9),(w_knight,3),(w_bishop,3),(w_rook,5),(w_pawn,1),(b_king,0),(b_queen,-9),(b_knight,-3),(b_bishop,-3),(b_rook,-5),(b_pawn,-1)}
);

// evaluate (factor for special_pawns and moves need to be find by tests)
evaluate == (
    200 * kings // # white kings - # black kings
    + SIGMA(z).(z : figures_to_values[ran(white) \/ ran(black)] | z) // all other figures
    + 1 * special_pawns(white, black) // # doubled, isolated and backward white pawns - # doubled, isolated and backward black pawns
    + 2 * semi_open_files(white, black) // # open files white - # open files black (at least 5 fields to move into one direction)
    + 2 * adjacent_king_fields(white, black) // attack on white - black kings adjacent fields
    + 3 * control_center(white, black) // difference between white and black pawn at center
)
ASSERTIONS
  dom({x,d|in_order_interval(x,d,1,8)}) = 2..7;
  dom({x,d|in_order_interval(x,d,8,1)}) = 2..7
OPERATIONS
  // execute a promition for a white pawn
  white_promotion(x, new_figure) =
    PRE
      fifty < 100 &
      moving = TRUE &
      new_figure : WHITE_FIGURES - {w_king, w_pawn} &
      x : 1..8
    THEN
      ANY a, new_white, new_black
      WHERE
        ((a,7),w_pawn) : white &
        x : {a-1, a, a+1} &
        new_black <: black &
        new_white = (white <+ {((x,8),new_figure)}) - {((a,7),w_pawn)} &
        (x = a =>
          free(a, 8, white, black) &
          new_black = black &
          move_white_pawn(a, 7, a, 8, 0, white, black)) &
        (x : {a-1, a+1} =>
          (x,8) : dom(black) &
          new_black = black - {((x,8),black((x,8)))} &
          move_white_pawn(a, 7, x, 8, 1, white, black)) &
        not_in_check_white(new_white, new_black)
      THEN
        white := new_white ||
        black := new_black ||
        moving := FALSE ||
        en_passant := 0 ||
        IF not_in_check_black(new_white, new_black) THEN in_check := FALSE ELSE in_check := TRUE END ||
        fifty := 0
      END // any
    END; // pre
  // execute a promition for a black pawn
  black_promotion(x, new_figure) =
    PRE
      fifty < 100 &
      moving = FALSE &
      new_figure : BLACK_FIGURES - {b_king, b_pawn} &
      x : 1..8
    THEN
      ANY a, new_white, new_black
      WHERE
        ((a,2),b_pawn) : black &
        x : {a-1, a, a+1} &
        new_white <: white &
        new_black = (black <+ {((x,1),new_figure)}) - {((a,2),b_pawn)} &
        (x = a =>
          free(a, 1, white, black) &
          new_white = white &
          move_black_pawn(a, 2, a, 1, 0, white, black)) &
        (x : {a-1, a+1} =>
          (x,1) : dom(white) &
          new_white = white - {((x,1),white((x,1)))} &
          move_black_pawn(a, 2, x, 1, 1, white, black)) &
        not_in_check_black(new_white, new_black)
    THEN
      white := new_white ||
      black := new_black ||
      moving := TRUE ||
      en_passant := 0 ||
      IF not_in_check_white(new_white, new_black) THEN in_check := FALSE ELSE in_check := TRUE END ||
      fifty := 0
      END // any
    END; // pre
  // execute a white en_passant move
  white_en_passant =
    PRE
      fifty < 100 &
      moving = TRUE
    THEN
      ANY a, b, new_white, new_black
      WHERE
        ((a,b),w_pawn) : white &
        en_passant /= 0 &
        b = 5 & a : {en_passant-1,en_passant+1} &
        new_white = (white <+ {((en_passant,b+1),w_pawn)}) - {((a,b),w_pawn)} &
        new_black = black - {((en_passant,5),b_pawn)} &
        not_in_check_white(new_white, new_black)
      THEN
        white := new_white ||
        black := new_black ||
        moving := FALSE ||
        en_passant := 0 ||
        IF not_in_check_black(new_white, new_black) THEN in_check := FALSE ELSE in_check := TRUE END ||
        fifty := 0
      END // any
    END; // pre
  // execute a black en_passant move
  black_en_passant =
    PRE
      fifty < 100 &
      moving = FALSE
    THEN
      ANY a, b, new_white, new_black
      WHERE
        ((a,b),b_pawn) : black &
        en_passant /= 0 &
        b = 4 & a : {en_passant-1,en_passant+1} &
        new_white = white - {((en_passant,4),w_pawn)} &
        new_black = (black <+ {((en_passant,b-1),b_pawn)}) - {((a,b),b_pawn)} &
        not_in_check_black(new_white, new_black)
      THEN
        white := new_white ||
        black := new_black ||
        moving := TRUE ||
        en_passant := 0 ||
        IF not_in_check_white(new_white, new_black) THEN in_check := FALSE ELSE in_check := TRUE END ||
        fifty := 0
      END // any
    END; // pre
  // execute a white castling move to a given side
  white_castling(side) =
    PRE
      fifty < 100 &
      in_check = FALSE &
      side : SIDES &
      moving = TRUE
    THEN
      ANY king, rook, rook_old, new_white
      WHERE
        castling_status(W,side) = TRUE &
        king : {3,7} &
        rook : {4,6} &
        rook_old : {1,8} &
        ((5,1),w_king) : white &
        new_white = (white <+ {((king,1),w_king),((rook,1),w_rook)}) - {((5,1),w_king),((rook_old,1),w_rook)} &
        (side = kingside =>
          ((8,1),w_rook) : white &
          king = 7 &
          rook = 6 &
          rook_old = 8 &
          !(i).(i : 6..7 => free(i,1,white,black) &
            not(#(j,k,fig).(((j,k),fig) : black & move_black_piece(fig,j,k,i,1,1,white,black))))) &
        (side = queenside =>
          ((1,1),w_rook) : white &
          king = 3 &
          rook = 4 &
          rook_old = 1 &
          !(i).(i : 2..4 => free(i,1,white,black)) &
          !(j).(j : 3..4 =>
            not(#(m,n,fig).(((m,n),fig) : black & move_black_piece(fig,m,n,j,1,1,white,black))))) &
        not_in_check_white(new_white, black)
      THEN
        white := new_white ||
        moving := FALSE ||
        en_passant := 0 ||
        IF not_in_check_black(new_white, black) THEN in_check := FALSE ELSE in_check := TRUE END ||
        castling_status := castling_status <+ {((W,kingside),FALSE),((W,queenside),FALSE)} ||
        fifty := fifty + 1
      END // where
    END; // pre
  // execute a black castling move to a given side
  black_castling(side) =
    PRE
      fifty < 100 &
      in_check = FALSE &
      side : SIDES &
      moving = FALSE
    THEN
      ANY king, rook, rook_old, new_black
      WHERE
        castling_status(B,side) = TRUE &
        king : {3,7} &
        rook : {4,6} &
        rook_old : {1,8} &
        ((5,8),b_king) : black &
        new_black = (black <+ {((king,8),b_king),((rook,8),b_rook)}) - {((5,8),b_king),((rook_old,8),b_rook)} &
        (side = kingside =>
          ((8,8),b_rook) : black &
          king = 7 &
          rook = 6 &
          rook_old = 8 &
          !(i).(i : 6..7 => free(i,8,white,black) &
            not(#(j,k,fig).(((j,k),fig) : white & move_white_piece(fig,j,k,i,8,1,white,black))))) &
        (side = queenside =>
          ((1,8),b_rook) : black &
          king = 3 &
          rook = 4 &
          rook_old = 1 &
          !(i).(i : 2..4 => free(i,8,white,black)) &
          !(j).(j : 3..4 =>
            not(#(m,n,fig).(((m,n),fig) : white & move_white_piece(fig,m,n,j,8,1,white,black))))) &
        not_in_check_black(white, new_black)
      THEN
        black := new_black ||
        moving := TRUE ||
        en_passant := 0 ||
        IF not_in_check_white(white, new_black) THEN in_check := FALSE ELSE in_check := TRUE END ||
        castling_status := castling_status <+ {((B,kingside),FALSE),((B,queenside),FALSE)} ||
        fifty := fifty + 1
      END // where
    END; // pre
  // white figure on (a,b) move to (x,y) and eventually take an opponent figure
  move_white(figure, a, b, x, y, take) =
    PRE
      fifty < 100 &
      figure : ran(white) &
      x : 1..8 & y : 1..8 &
      take : {0,1} &
      moving = TRUE &
      ((a,b),figure) : white &
      (a,b) /= (x,y) &
      (figure = w_pawn => y : 3..7) &
      IF take = 1 THEN
        (x,y) : dom(black) &
        not_in_check_white((white <+ {((x,y),figure)}) - {((a,b),figure)}, black - {((x,y),black((x,y)))})
      ELSE
        not_in_check_white((white <+ {((x,y),figure)}) - {((a,b),figure)}, black)
      END &
      move_white_piece(figure, a, b, x, y, take, white, black)
    THEN
      moving := FALSE ||
      white := (white <+ {((x,y),figure)}) - {((a,b),figure)} ||
      IF take = 1 THEN
        black := black - {((x,y),black((x,y)))} ||
        IF not_in_check_black((white <+ {((x,y),figure)}) - {((a,b),figure)}, black - {((x,y),black((x,y)))}) THEN in_check := FALSE ELSE in_check := TRUE END
      ELSE
        IF not_in_check_black((white <+ {((x,y),figure)}) - {((a,b),figure)}, black) THEN in_check := FALSE ELSE in_check := TRUE END
      END ||
      IF (b = 2 & y = 4 & figure = w_pawn) THEN en_passant := a ELSE en_passant := 0 END ||
      IF figure = w_pawn or take = 1 THEN fifty := 0 ELSE fifty := fifty + 1 END ||
      IF figure = w_king THEN castling_status := castling_status <+ {((W,kingside),FALSE),((W,queenside),FALSE)} ELSE
        IF figure = w_rook & a = 8 & b = 1 THEN castling_status(W,kingside) := FALSE ELSE
          IF figure = w_rook & a = 1 & b = 1 THEN castling_status(W,queenside) := FALSE END END END
    END; // pre
  // black figure on (a,b) move to (x,y) and eventually take an opponent figure
  move_black(figure, a, b, x, y, take) =
    PRE
      fifty < 100 &
      figure : ran(black) &
      x : 1..8 & y : 1..8 &
      take : {0,1} &
      moving = FALSE &
      ((a,b),figure) : black &
      (a,b) /= (x,y) &
      (figure = b_pawn => y : 2..7) &
      IF take = 1 THEN
        (x,y) : dom(white) &
        not_in_check_black(white - {((x,y),white((x,y)))}, (black <+ {((x,y),figure)}) - {((a,b),figure)})
      ELSE
        not_in_check_black(white, (black <+ {((x,y),figure)}) - {((a,b),figure)})
      END &
      move_black_piece(figure, a, b, x, y, take, white, black)
    THEN
      moving := TRUE ||
      black := (black <+ {((x,y),figure)}) - {((a,b),figure)} ||
      IF take = 1 THEN
        white := white - {((x,y),white((x,y)))} ||
        IF not_in_check_white(white - {((x,y),white((x,y)))}, (black <+ {((x,y),figure)}) - {((a,b),figure)}) THEN in_check := FALSE ELSE in_check := TRUE END
      ELSE
        IF not_in_check_white(white, (black <+ {((x,y),figure)}) - {((a,b),figure)}) THEN in_check := FALSE ELSE in_check := TRUE END
      END ||
      IF (b = 7 & y = 5 & figure = b_pawn) THEN en_passant := a ELSE en_passant := 0 END ||
      IF figure = b_pawn or take = 1 THEN fifty := 0 ELSE fifty := fifty + 1 END ||
      IF figure = b_king THEN castling_status := castling_status <+ {((B,kingside),FALSE),((B,queenside),FALSE)} ELSE
        IF figure = b_rook & a = 8 & b = 8 THEN castling_status(B,kingside) := FALSE ELSE
          IF figure = b_rook & a = 1 & b = 8 THEN castling_status(B,queenside) := FALSE END END END
    END; // pre
  // eval
  evalState =
    BEGIN
      value := evaluate
    END;
  // tests
  test_promotion =
    BEGIN
      white := {((2,7),w_pawn),((8,2),w_king),((3,1),w_queen)} ||
      black := {((2,2),b_pawn),((8,7),b_king),((3,8),b_queen)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_en_passant =
    BEGIN
      white := {((5,5),w_pawn),((5,1),w_king)} ||
      black := {((4,7),b_pawn),((5,8),b_king)} ||
      moving := FALSE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_castling =
    BEGIN
      white := {((5,1),w_king),((8,1),w_rook)} ||
      black := {((5,8),b_king),((1,8),b_rook)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_checkmate =
    BEGIN
      white := {((5,1),w_king),((4,2),w_pawn),((5,2),w_pawn),((4,1),w_queen),((6,1),w_bishop)} ||
      black := {((5,8),b_king),((8,4),b_queen)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_checkmate_2 =
    BEGIN
      white := {((5,6),w_king),((5,7),w_queen)} ||
      black := {((5,8),b_king)} ||
      moving := FALSE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_checkmate_3 =
    BEGIN
      white := {((8,2),w_king)} ||
      black := {((8,4),b_rook),((6,2),b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_king_movement =
    BEGIN
      white := {((4,4),w_king)} ||
      black := {((5,8),b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_queen_movement =
    BEGIN
      white := {((4,4),w_queen),((5,1),w_king)} ||
      black := {((5,8),b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_rook_movement =
    BEGIN
      white := {((4,4),w_rook),((5,1),w_king)} ||
      black := {((5,8),b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_bishop_movement =
    BEGIN
      white := {((4,4),w_bishop),((5,1),w_king)} ||
      black := {((5,8),b_king)} ||
      moving := TRUE ||
      fifty := 0
    END;
  test_knight_movement =
    BEGIN
      white := {((4,4),w_knight),((5,1),w_king)} ||
      black := {((5,8),b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_pawn_movement =
    BEGIN
      white := {((4,4),w_pawn),((5,1),w_king)} ||
      black := {((5,8),b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_pin =
    BEGIN
      white := {((5,1),w_king),((8,5),w_queen)} ||
      black := {((5,8),b_king),((7,6),b_rook)} ||
      moving := FALSE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_fork =
    BEGIN
      white := {((5,1),w_king),((3,7),w_knight)} ||
      black := {((5,8),b_king),((1,8),b_rook)} ||
      moving := FALSE ||
      en_passant:= 0 ||
      in_check := TRUE ||
      fifty := 0
    END;
  test_double_check =
    BEGIN
      white := {((5,1),w_king),((6,1),w_rook),((6,4),w_bishop)} ||
      black := {((6,8),b_king),((4,8),b_queen)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 0
    END;
  test_movement_remis =
    BEGIN
      white := {((5,1),w_king)} ||
      black := {((8,1),b_king)} ||
      moving := TRUE ||
      en_passant:= 0 ||
      fifty := 99
    END;
  test_remis =
    BEGIN
      white := {((8,1),w_king)} ||
      black := {((5,8),b_king),((7,3),b_queen)} ||
      moving := TRUE ||
      en_passant := 0 ||
      fifty := 0
    END
END
