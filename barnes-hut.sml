structure BarnesHut =
struct

  open Mechanics
  structure BB = BoundingBox
  open Plane
  open TestData

  infixr 3 ++
  infixr 4 **
  infixr 4 //
  infixr 3 -->

  datatype bhtree =
      Empty
    | Single of body
    | Cell of (Scalar.scalar * Plane.point) * BB.bbox * bhtree * bhtree * bhtree * bhtree
      (* ((mass, center), box, top-left, top-right, bottom-left, bottom-right) *)

  (* Projects the mass and center from the root node of a bhtree *)
  fun center_of_mass (T : bhtree) : Scalar.scalar * Plane.point =
      case T of
          Empty => (Scalar.zero, Plane.origin)
        | Single (m, p, _) => (m, p)
        | Cell (com, _, _,_,_,_) => com

  (* Note: Doesn't compare velocities as these are unaffected by compute_tree *)
  fun bodyEq ((m1, p1, _) : body, (m2, p2, _) : body) : bool =
      (Scalar.eq (m1, m2)) andalso Plane.pointEqual (p1, p2)

  fun bhtreeEq (t1 : bhtree, t2 : bhtree) : bool =
      case (t1, t2) of
          (Empty, Empty) => true
        | (Single b1, Single b2) => bodyEq (b1, b2)
        | (Cell ((cm1, cp1), bb1, tl1,tr1,bl1,br1), Cell ((cm2, cp2), bb2, tl2,tr2,bl2,br2)) =>
              Scalar.eq (cm1, cm2) andalso
              Plane.pointEqual (cp1, cp2) andalso
              BB.equal (bb1, bb2) andalso 
              bhtreeEq (tl1,tl2) andalso bhtreeEq (tr1,tr2) andalso 
              bhtreeEq (bl1,bl2) andalso bhtreeEq (br1,br2)
        | (_, _) => false

  (* ---------------------------------------------------------------------- *)
  (* TASKS *)

  (* TASK *)
  (* Compute the barycenter of four points.
     Assumes that all points have nonnegative mass, and 
     that at least one point has strictly positive mass. *)
  fun barycenter ((m1,p1) : (Scalar.scalar * Plane.point),
                  (m2,p2) : (Scalar.scalar * Plane.point),
                  (m3,p3) : (Scalar.scalar * Plane.point),
                  (m4,p4) : (Scalar.scalar * Plane.point)) : Scalar.scalar * Plane.point =
    let
      val totalMass = Scalar.plus(m1, Scalar.plus(m2, Scalar.plus(m3, m4)))
      val totalRVec = (origin --> p1) ** m1 ++ (origin --> p2) ** m2 ++ (origin --> p3) ** m3 ++ (origin --> p4) ** m4
    in
      (totalMass, head(totalRVec // totalMass))
    end

  (* TASK *)
  (* Compute the four quadrants of the bounding box *)
  fun quarters (bb : BB.bbox) : BB.bbox * BB.bbox * BB.bbox * BB.bbox =
      let
        val (tlc, trc, blc, brc) = BB.corners(bb)
        val center = BB.center(bb)
      in
        (BB.from2Points(tlc, center), BB.from2Points(trc, center), BB.from2Points(blc, center), BB.from2Points(brc, center))
      end

  (* Test for quarters*)
  val true = let val (tl,tr,bl,br) = quarters(bb4) 
             in BB.equal(tl,bb0) andalso BB.equal(tr,bb1) andalso
                BB.equal(bl, bb2) andalso BB.equal(br,bb3)
             end

  (* TASK *)
  (* Computes the Barnes-Hut tree for the bodies in the given sequence.
   * Assumes all the bodies are contained in the given bounding box,
     and that no two bodies have collided (or are so close that dividing the 
     bounding box will not eventually separate them).
     *)
  fun compute_tree (s : body Seq.seq) (bb : BB.bbox) : bhtree = 
    case Seq.length s of
      0 => Empty
    | 1 => Single(Seq.nth 0 s)
    | _ => (let
              val (tl, tr, bl, br) = quarters(bb)
              val stl = Seq.filter (fn x => BB.contained (false, false, false, false) (position x,tl)) s
              val str = Seq.filter (fn x => BB.contained (true, false, false, false) (position x,tr)) s
              val sbl = Seq.filter (fn x => BB.contained (false, false, true, false) (position x,bl)) s
              val sbr = Seq.filter (fn x => BB.contained (true, false, true, false) (position x,br)) s
              val treetl = compute_tree stl tl
              val treetr = compute_tree str tr
              val treebl = compute_tree sbl bl
              val treebr = compute_tree sbr br
            in
              Cell(barycenter(center_of_mass(treetl), center_of_mass(treetr), center_of_mass(treebl), center_of_mass(treebr)), bb, 
                    treetl, treetr, treebl, treebr)
            end)
  (* Test for compute_tree*)
  val three_bodies = Seq.cons body1 (Seq.cons body2 (Seq.cons body3 (Seq.empty())))
  val three_bodies_tree = Cell ((Scalar.fromInt 3, p22), bb4,
                                Cell ((Scalar.fromInt 2, p13), bb0,
                                      Single body3, Empty, Empty, Single body2), 
                                Empty, 
                                Empty, 
                                Single body1)
  val true = bhtreeEq (compute_tree three_bodies bb4, three_bodies_tree)
  

  (* TASK *)
  (* too_far p1 p2 bb t determines if point p1 is "too far" from 
   * a region bb with barycenter p2, given a threshold parameter t,
   * for it to be worth recuring into the region
   *)
  fun too_far (p1 : Plane.point) (p2 : Plane.point) (bb : BB.bbox) (t : Scalar.scalar) : bool = 
    Scalar.lte(Scalar.divide(BB.diameter(bb),(distance p1 p2)), t)

  (* TASK *)
  (* Computes the acceleration on b from the tree T using the Barnes-Hut
   * algorithm with threshold t
   *)
  fun bh_acceleration (T : bhtree) (t : Scalar.scalar) (b : body) : Plane.vec =
    case T of
      Empty => zero
    | Single(e) => accOn (b,e)
    | Cell((m, bcenter), bb, treetl, treetr, treebl, treebr) => case too_far (position b) bcenter bb t of
                                                                  true => accOn(b, (m, bcenter, zero))
                                                                | false => (bh_acceleration treetl t b) ++ (bh_acceleration treetr t b) ++ (bh_acceleration treebl t b) ++ (bh_acceleration treebr t b)
                                                                  (*( let
                                                                    val acctl =
                                                                      case treetl of
                                                                        Empty => zero
                                                                      | Single(e) => accOn (b,e)
                                                                      | Cell((m, bcenter), bb', tree1, tree2, tree3, tree4) => case too_far (position b) bcenter bb' t of
                                                                                                                                  true => accOn(b, (m, bcenter, zero))
                                                                                                                                | false => bh_acceleration treetl t b
                                                                    val acctr =
                                                                      case treetr of
                                                                        Empty => zero
                                                                      | Single(e) => accOn (b,e)
                                                                      | Cell((m, bcenter), bb', tree1, tree2, tree3, tree4) => case too_far (position b) bcenter bb' t of
                                                                                                                                  true => accOn(b, (m, bcenter, zero))
                                                                                                                                | false => bh_acceleration treetr t b
                                                                    
                                                                    val accbl =
                                                                      case treebl of
                                                                        Empty => zero
                                                                      | Single(e) => accOn (b,e)
                                                                      | Cell((m, bcenter), bb', tree1, tree2, tree3, tree4) => case too_far (position b) bcenter bb' t of
                                                                                                                                  true => accOn(b, (m, bcenter, zero))
                                                                                                                                | false => bh_acceleration treebl t b
                                                                    val accbr =
                                                                      case treebr of
                                                                        Empty => zero
                                                                      | Single(e) => accOn (b,e)
                                                                      | Cell((m, bcenter), bb', tree1, tree2, tree3, tree4) => case too_far (position b) bcenter bb' t of
                                                                                                                                  true => accOn(b, (m, bcenter, zero))
                                                                                                                                | false => bh_acceleration treebr t b                                        
                                                                  in
                                                                    acctl ++ acctr ++ accbl ++ accbr
                                                                  end)*)

  (* TASK
     Given a threshold and a sequence of bodies, compute the acceleration
     on each body using the Barnes-Hut algorithm.
   *)
  fun barnes_hut (threshold : Scalar.scalar) (s : body Seq.seq) : Plane.vec Seq.seq =
    let
      val positionSeq = Seq.map (fn x => position x) s
      val tree = compute_tree s (BB.fromPoints positionSeq)
    in
      Seq.map (fn x => bh_acceleration tree threshold x) s
    end
    

  (* Default value of the threshold, theta = 0.5 *)
  val threshold = (Scalar.fromRatio (1,2))

  val accelerations : body Seq.seq -> Plane.vec Seq.seq = barnes_hut threshold

end
