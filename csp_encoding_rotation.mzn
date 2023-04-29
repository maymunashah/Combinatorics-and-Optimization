include "globals.mzn";
int: plate_width;
int: n;
set of int: ELEMENTS = 1..n;
set of int: DOUBLE_ELEMENTS = 1..n*2;
array[ELEMENTS] of int: x_cord;
array[ELEMENTS] of int: y_cord;
array[ELEMENTS] of int: max_y_recpermutation = [max([x_cord[el], y_cord[el]])| el in ELEMENTS];
int: max_y = sum(max_y_recpermutation);
int: min_y = max(y_cord);
var min_y..max_y: y;

int: k = 2;
set of int: DIMENSIONS = 1..k;
array[DIMENSIONS] of int: l                            = [0,0];
array[DIMENSIONS] of var int: u                        = [plate_width, y];
array[DOUBLE_ELEMENTS,DIMENSIONS] of int: rect_size    = array2d(DOUBLE_ELEMENTS, DIMENSIONS, 
                                                         [ if j = 1 then x_cord[i] else y_cord[i] endif|
                                                         i in ELEMENTS, j in DIMENSIONS] ++ 
                                                         [ if j = 1 then y_cord[i] else x_cord[i] endif|
                                                         i in ELEMENTS, j in DIMENSIONS]);
array[DOUBLE_ELEMENTS,DIMENSIONS] of int: rect_offset  = array2d(DOUBLE_ELEMENTS, DIMENSIONS, 
                                                         [ 0 |i in DOUBLE_ELEMENTS, j in DIMENSIONS]);
array[DOUBLE_ELEMENTS] of set of DOUBLE_ELEMENTS:shape = [{i} | i in DOUBLE_ELEMENTS];                                                         
array[ELEMENTS,DIMENSIONS] of var 0..max([plate_width,max_y])-1: x;
array[ELEMENTS] of var DOUBLE_ELEMENTS: kind;


constraint geost_bb( k,
                 rect_size,
                 rect_offset,
                 shape,
                 x,
                 kind,
                 l,
                 u);
                             
array[ELEMENTS] of set of DOUBLE_ELEMENTS: valid_shapes;

valid_shapes = [array2set(shape[el]++shape[el+n])| el in ELEMENTS];
constraint forall (el in ELEMENTS) (
    kind[el] in valid_shapes[el]
);

array[ELEMENTS] of var 0..plate_width- min(min(x_cord), min(y_cord)): x_caret;
array[ELEMENTS] of var 0..max_y-min(min(x_cord), min(y_cord)): y_caret;

constraint forall(i in ELEMENTS, val in 0..plate_width-1)(
    x_caret[i] == val <-> x[i,1] == val             
);
constraint forall(i in ELEMENTS, val in 0..max_y-1)(
    y_caret[i] == val <-> x[i,2] == val             
);

int: dm_rec = arg_max(x_cord);
set of int: ELEMENTS_diff_dm_rec = ELEMENTS diff dm_rec..dm_rec;

int: min_dm_size = min(x_cord[dm_rec], y_cord[dm_rec]);
constraint y_caret[dm_rec]  <= (y - min_dm_size)/2;
constraint x_caret[dm_rec] <= round((plate_width - min_dm_size)/2);

constraint forall(o in ELEMENTS_diff_dm_rec)(y_caret[o] <= y - min(x_cord[o], y_cord[o]));
constraint forall(o in ELEMENTS_diff_dm_rec)(x_caret[o] <= plate_width - min(x_cord[o], y_cord[o]));
 
ann: search_ann1 = int_search(x, dom_w_deg, indomain_random);  
ann: search_ann2 = int_search(x_caret, dom_w_deg, indomain_random); 
ann: search_ann3 = int_search(y_caret, dom_w_deg, indomain_random);  

include "gecode.mzn";
solve 
  :: search_ann1
  :: search_ann2
  :: search_ann3
  :: restart_luby(300)
  :: relax_and_reconstruct(y_caret, 85)
minimize y;

