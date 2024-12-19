module PulseTutorialExercises.TruncatePoint
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Box
module Box = Pulse.Lib.Box
noeq
type point = {
    x:box int;
    y:box int
}

let is_point (p:point) (xy:int & int) =
  pts_to p.x (fst xy) **
  pts_to p.y (snd xy)


ghost
fn fold_is_point (x y:box int) (#a #b:int)
requires pts_to x a ** pts_to y b
ensures (is_point {x; y} (a, b))
{
    let p = { x; y };
    rewrite each x as p.x, y as p.y;
    fold (is_point p (a, b));
    rewrite each p as ({x;y});
}



fn new_point (x y : int)
requires emp
returns p:point
ensures is_point p (x, y)
{
   admit()
}


let truncate (p1 p2: (int & int)) =
    let min x y = if x < y then x else y in
    let (x1, y1) = p1 in
    let (x2, y2) = p2 in
    min x1 x2, min y1 y2
    

fn trunc (p1 p2:point)
requires is_point p1 'v1 ** is_point p2 'v2
ensures  is_point p1 'v1 ** is_point p2 (truncate 'v1 'v2)
{
    admit()
}
