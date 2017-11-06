(* 3-d vector *)
type vec3 = { x:float; y:float; z:float }
let ( *@ ) k v = { x = k *. v.x; y = k *. v.y; z = k *. v.z }
let ( +@ ) a b = { x = a.x +. b.x; y = a.y +. b.y; z = a.z +. b.z }
let ( -@ ) a b = { x = a.x -. b.x; y = a.y -. b.y; z = a.z -. b.z }
let ( *@@ ) a b = { x = a.x *. b.x; y = a.y *. b.y; z = a.z *. b.z }
let dot    a b = a.x *. b.x +. a.y *. b.y +. a.z *. b.z
let len a = sqrt ( dot a a )
let unit a = let norm = 1. /. (len a) in norm *@ a
let cross a b = {
  x = a.y *. b.z -. a.z *. b.y;
  y = a.z *. b.x -. a.x *. b.z;
  z = a.x *. b.y -. a.y *. b.x;
}

(* ray *)
type ray = { o: vec3; d: vec3 }
let point_at r t = r.o +@ (t *@ r.d)

(* camera *)
type camera = { 
  llc: vec3; horizontal: vec3; vertical: vec3; origin: vec3;
  lens_r: float; u: vec3; v: vec3 }

let make_camera from at vup fov aspect aparture dof =
  let pi = 4.0 *. atan 1.0 in
  let theta = fov *. pi /. 180. in
  let dhh = dof *. tan (theta /. 2.) in
  let dhw = aspect *. dhh in
  let w = unit (from -@ at) in
  let u = unit (cross vup w) in
  let v = cross w u in
  {
    llc = from -@ (dhw *@ u) -@ (dhh *@ v) -@ (dof *@ w);
    horizontal = 2. *. dhw *@ u;
    vertical = 2. *. dhh *@ v;
    origin = from;
    lens_r = aparture /. 2.;
    u = u; v = v
  }

let get_ray { llc; horizontal; vertical; origin; lens_r; u; v } s t =
  let rec rnd_disk () =
    match { x = 2. *. (Random.float 1.) -. 1.;
            y = 2. *. (Random.float 1.) -. 1.;
            z = 0. } with
      | p when (dot p p) < 1. -> p
      | _ -> rnd_disk () in
  let rd = lens_r *@ rnd_disk () in
  let offset = rd.x *@ u +@ rd.y *@ v  in
  { o = origin +@ offset;
    d = llc +@ (s *@ horizontal) +@ (t *@ vertical) -@ origin -@ offset }

(* hit *)
type hit = { t: float; p: vec3; n: vec3 }

let sphere center radius ray tmin tmax =
  let oc = ray.o -@ center in
  let a = dot ray.d ray.d in
  let b = dot oc ray.d in
  let c = (dot oc oc) -. (radius *. radius) in
  let d2 = (b *. b) -. (a *. c) in
  if d2 > 0. then
    let d = sqrt d2 in
    let t1 = (-. b -. d) /. a in
    let t2 = (-. b +. d) /. a in
    let ret t =
      let p = point_at ray t in 
      Some { t = t; p = p; n = 1. /. radius *@ (p -@ center)  } 
    in
    if t1 < tmax && t1 > tmin then
      ret t1
    else if t2 < tmax && t2 > tmin then
      ret t2
    else
      None
  else
    None

let world_hit objs ray tmin tmax =
  let f acc (h, mat) =
    match (h ray tmin (snd acc)) with
      | Some a -> (Some (a, mat), a.t)
      | None -> acc
  in fst (List.fold_left f (None, tmax) objs)

(* materials/helper *)
let random_in_unit_shpere () = 
  { x = 2. *. (Random.float 1.) -. 1.;
    y = 2. *. (Random.float 1.) -. 1.;
    z = 2. *. (Random.float 1.) -. 1. }
let reflect v n = v -@ (2. *. dot v n) *@ n
let refract v n r =
  let uv = unit v in
  let dt = dot uv n in
  let d = 1.0 -. r *. r *. (1.0 -. dt *. dt) in
  if d > 0. then Some (r *@ (uv -@ dt *@ n) -@ (sqrt d) *@ n)
  else None

type obj_type = 
  | Material of ray * vec3
  | Light of vec3

let light att r re =
  let dn = dot re.n (unit r.d) in
  Light (0.5 *. (1. -. dn) *@ att)

(* materials *)
let labertarian_mat att r re = 
  let target = re.n +@ random_in_unit_shpere () in
  Material ({ o = re.p; d = target }, att)

let metal_mat att fuzz r re = 
  let reflect v n = v -@ (2. *. dot v n) *@ n in
  let d = reflect (unit r.d) re.n in
  Material ({ o = re.p; d = d +@ (fuzz *@ random_in_unit_shpere ()) }, att)

let dialectric_mat ri r re = 
  let att = { x = 1.; y = 1.; z = 1.; } in
  let rec pow x n = if n = 0 then 1. else x *. pow x (n-1) in
  let refl = reflect r.d re.n in
  let dn = dot r.d re.n in
  let (on, ratio, cosi) = 
    if dn > 0. then (-1. *@ re.n, ri, ri *. dn /. len r.d)
               else (re.n, 1.0 /. ri, -. dn /. len r.d) in
  let schlick = 
    let r = pow ((1. -. ri) /. (1. +. ri)) 2 in
    r +. (1. -. r) *. (pow (1. -. cosi) 5) in
  Material ({ o = re.p;
    d = match refract r.d on ratio with 
        | Some refr when (Random.float 1.0) > schlick -> refr
        | _ -> refl
  }, att)

(* trace *)
let color r world =
  let rec go r depth acc =
    match world_hit world r 0.001 max_float with
      | Some (re, mat) -> (* hit *)
        if depth < 50 then
          match mat r re with 
            | Material (s,a) -> go s (depth+1) (a *@@ acc)
            | Light a -> a *@@ acc
        else
          { x = 0.; y = 0.; z = 0. }
      | None -> (* sky *) 
          { x = 0.; y = 0.; z = 0. }
  in
    go r 0 { x = 1.; y = 1.; z = 1. }

let antialias f ns =
  let rec go ns acc =
    match ns with
      | 0 -> acc
      | n -> go (ns - 1) (acc +@ f ()) in
  let c = (1. /. float_of_int ns) *@ (go ns {x = 0.; y = 0.; z = 0.}) in
  { x = sqrt c.x; y = sqrt c.y; z = sqrt c.z }

let make_random_world () = 
  let rec range2 a b acc = 
    let rec range (n1, n2) acc0 = if n1 = n2 then acc0 else range (n1, n2 - 1) (n2 :: acc0) in
      match b with
      | (n,m) when n = m -> acc
      | (n,m) -> range2 a (n, m - 1) ((List.map (fun s -> (s,m)) (range a [])) @ acc)
  in
  let rec omap f l = match l with
    | [] -> []
    | x :: xs -> match f x with 
                   | Some fx -> fx :: omap f xs
                   | None    -> omap f xs
  in
  let ground = (sphere {x = 0.; y = -1000.; z = 0.} 1000.,
                labertarian_mat {x = 1.; y = 1.; z = 1.}) in
  let spread (a,b) = 
    let r () = Random.float 1. in
    let r2 () = r() *. r () in
    let ra () = 0.5 *. (1. +. r()) in
    let c = { x = float_of_int a +. 0.9 *. r ();
              y = 0.2;
              z = float_of_int b +. 0.9 *. r () } in
    if len (c -@ { x = 4.; y = 0.2; z = 0.}) > 0.9 then
      Some (sphere c 0.2,
       match r() with
        | p when p < 0.2 -> labertarian_mat {x = r2 (); y = r2 (); z = r2 ()}
        | p when p < 0.3 -> metal_mat {x = ra (); y = ra (); z = ra ()} (0.5 *. r ())
        | p when p < 0.6 -> light {x = ra (); y = ra (); z = ra ()}
        | _ -> dialectric_mat 1.5
      )
    else
      None
  in 
    ground :: (omap spread (range2 (-11,10) (-11,10) [])) @
    [
      (sphere { x = 0.; y = 1.; z = 0. } 1., dialectric_mat 1.5);
      (sphere { x = -4.; y = 1.; z = 0. } 1., labertarian_mat {x = 0.4; y = 0.2; z = 0.1});
      (sphere { x = 4.; y = 1.; z = 0. } 1., metal_mat {x = 0.7; y = 0.6; z = 0.5} 0.);
    ]

(* member *)
let () =
  let width = 800 in
  let height = 400 in 
  let lookfrom = { x = 13.; y = 2.; z = 3. } in
  let lookat = { x = 0. ; y = 0.; z = 0. } in
  let camera = make_camera 
    lookfrom lookat { x = 0. ; y = 1.; z = 0. }
    20.
    (float_of_int width /. float_of_int height)
    0.1 10.0
  in
  let ns = 100 in
  let world = make_random_world () in
    Printf.printf "P3\n%d %d\n255\n" width height;
    for j = height - 1 downto 0 do
      for i = 0 to width - 1 do
        let sample () = 
          let u = (float_of_int i +. Random.float 1.) /. (float_of_int width) in
          let v = (float_of_int j +. Random.float 1.) /. (float_of_int height) in
          color (get_ray camera u v) world in
        let col = antialias sample ns in
        let ir = int_of_float (255.9 *. col.x) in
        let ig = int_of_float (255.9 *. col.y) in
        let ib = int_of_float (255.9 *. col.z) in
        Printf.printf "%d %d %d\n" ir ig ib
      done;
    done
