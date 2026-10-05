import Mathlib.Tactic

namespace PerfectPower.RationalVoronoiPacket
abbrev Point := ℚ × ℚ × ℚ
abbrev Face := ℕ × ℕ × ℕ
abbrev Edge := ℕ × ℕ × ℚ

structure Mesh where
  vertices : ℕ
  faces : List Face
  signs : List ℤ
  edges : List Edge
  deriving Repr

structure Leaf where
  face : ℕ
  address : List ℕ
  winner : Option ℕ
  radius : ℚ
  upper : List ℚ
  lower : List ℚ
  deriving Repr

structure Packet where
  sites : List ℕ
  fields : List (List ℚ)
  paths : List (List (List ℕ))
  depth : ℕ
  leaves : List Leaf
  deriving Repr

def point (a b c : ℚ) : Point := (a,b,c)
def corners : List Point := [(1,0,0),(0,1,0),(0,0,1)]
def midpoint (p q : Point) : Point := ((p.1+q.1)/2,(p.2.1+q.2.1)/2,(p.2.2+q.2.2)/2)
def children (v : List Point) : List (List Point) :=
  let a:=v[0]?.getD (0,0,0); let b:=v[1]?.getD (0,0,0); let c:=v[2]?.getD (0,0,0)
  let ab:=midpoint a b; let bc:=midpoint b c; let ca:=midpoint c a
  [[a,ab,ca],[ab,b,bc],[ca,bc,c],[ab,bc,ca]]
def patch (address : List ℕ) : List Point :=
  address.foldl (fun v i => (children v)[i]?.getD []) corners

def edgeLength (m : Mesh) (a b : ℕ) : ℚ :=
  ((m.edges.find? (fun e => decide ((e.1=a ∧ e.2.1=b) ∨ (e.1=b ∧ e.2.1=a)))).map (·.2.2)).getD 0

def faceVertices (f : Face) : List ℕ := [f.1,f.2.1,f.2.2]
def gram (m : Mesh) (f : Face) : ℚ × ℚ × ℚ :=
  let A:=(edgeLength m f.1 f.2.1)^2
  let B:=(edgeLength m f.1 f.2.2)^2
  let C:=(A+B-(edgeLength m f.2.1 f.2.2)^2)/2
  (A,C,B)
def squared (g : ℚ × ℚ × ℚ) (p q : Point) : ℚ :=
  let u:=p.2.1-q.2.1; let v:=p.2.2-q.2.2
  g.1*u^2+2*g.2.1*u*v+g.2.2*v^2

def orientedEdges (f : Face) (sign : ℤ) : List (ℕ × ℕ) :=
  let a:=f.1; let b:=f.2.1; let c:=f.2.2
  if sign=1 then [(a,b),(b,c),(c,a)] else [(b,a),(c,b),(a,c)]

def reach (pairs : List (ℕ × ℕ)) (start budget : ℕ) : List ℕ :=
  Nat.iterate (fun known => (known ++ pairs.flatMap (fun p =>
    (if known.contains p.1 then [p.2] else []) ++ (if known.contains p.2 then [p.1] else []))).eraseDups) budget [start]

def vertexLink (m : Mesh) (v : ℕ) : List (ℕ × ℕ) :=
  m.faces.flatMap fun f =>
    if f.1=v then [(f.2.1,f.2.2)]
    else if f.2.1=v then [(f.1,f.2.2)]
    else if f.2.2=v then [(f.1,f.2.1)] else []

def faceKey (f : Face) : Face :=
  let low:=min f.1 (min f.2.1 f.2.2)
  let high:=max f.1 (max f.2.1 f.2.2)
  (low,f.1+f.2.1+f.2.2-low-high,high)

def meshCheck (m : Mesh) : Bool :=
  let oriented := (m.faces.zip m.signs).flatMap fun fs => orientedEdges fs.1 fs.2
  let pairs := m.edges.map fun e => (e.1,e.2.1)
  decide (3 ≤ m.vertices) && decide (m.signs.length=m.faces.length) &&
  m.signs.all (fun s => decide (s=1 ∨ s = -1)) &&
  decide (pairs.eraseDups.length=pairs.length) &&
  decide ((m.faces.map faceKey).eraseDups.length=m.faces.length) &&
  m.edges.all (fun e => decide (e.1<e.2.1 ∧ e.2.1<m.vertices ∧ 0<e.2.2) &&
    decide ((oriented.filter (· == (e.1,e.2.1))).length=1) &&
    decide ((oriented.filter (· == (e.2.1,e.1))).length=1)) &&
  m.faces.all (fun f => (faceVertices f).all (fun v => decide (v<m.vertices)) &&
    decide (f.1≠f.2.1 ∧ f.1≠f.2.2 ∧ f.2.1≠f.2.2) &&
    (orientedEdges f 1).all (fun p => decide (0<edgeLength m p.1 p.2)) &&
    (let g:=gram m f; decide (0<g.1*g.2.2-g.2.1^2))) &&
  decide ((reach pairs 0 m.vertices).length=m.vertices) &&
  (List.range m.vertices).all (fun v =>
    let link:=vertexLink m v
    let vs:=(link.flatMap fun p => [p.1,p.2]).eraseDups
    decide (0<vs.length) && vs.all (fun w => decide ((link.filter fun p => p.1==w || p.2==w).length=2)) &&
    decide ((reach link (vs[0]?.getD 0) m.vertices).length=vs.length))

def fieldValue (f : List ℚ) (tri : Face) (p : Point) : ℚ :=
  p.1*(f[tri.1]?.getD 0)+p.2.1*(f[tri.2.1]?.getD 0)+p.2.2*(f[tri.2.2]?.getD 0)

def fieldCheck (m : Mesh) (f : List ℚ) : Bool :=
  decide (f.length=m.vertices) && m.faces.all (fun tri =>
    let g:=gram m tri
    let u:=(f[tri.2.1]?.getD 0)-(f[tri.1]?.getD 0)
    let v:=(f[tri.2.2]?.getD 0)-(f[tri.1]?.getD 0)
    decide (g.2.2*u^2-2*g.2.1*u*v+g.1*v^2 ≤ g.1*g.2.2-g.2.1^2))

def pathCost (m : Mesh) (path : List ℕ) : ℚ :=
  ((path.zip path.tail).map fun p => edgeLength m p.1 p.2).sum

def pathCheck (m : Mesh) (site target : ℕ) (path : List ℕ) : Bool :=
  decide (path.head?=some site) && decide (path.getLast?=some target) &&
  decide (path.length≤m.vertices) && path.all (fun v => decide (v<m.vertices)) &&
  (path.zip path.tail).all (fun p => decide (0<edgeLength m p.1 p.2))

def center (v : List Point) : Point :=
  ((v.map (·.1)).sum/3,(v.map (·.2.1)).sum/3,(v.map (·.2.2)).sum/3)

def leafCheck (m : Mesh) (p : Packet) (leaf : Leaf) : Bool :=
  let tri:=m.faces[leaf.face]?.getD (0,0,0)
  let g:=gram m tri; let vs:=patch leaf.address; let c:=center vs
  decide (leaf.face<m.faces.length ∧ leaf.address.length≤p.depth ∧ 0≤leaf.radius) &&
  leaf.address.all (fun i => decide (i<4)) &&
  decide (leaf.upper.length=p.sites.length ∧ leaf.lower.length=p.sites.length) &&
  vs.all (fun v => decide (squared g c v ≤ leaf.radius^2)) &&
  (List.range p.sites.length).all (fun i =>
    let site:=p.sites[i]?.getD 0
    let U:=leaf.upper[i]?.getD 0;let L:=leaf.lower[i]?.getD 0
    let paths:=p.paths[i]?.getD []
    decide (0≤L) &&
    ((List.range 3).any fun k =>
      let v:=(faceVertices tri)[k]?.getD 0
      let delta:=U-pathCost m (paths[v]?.getD [])
      decide (0≤delta ∧ squared g c (corners[k]?.getD (0,0,0))≤delta^2)) &&
    (decide (L=0) || p.fields.any (fun f => decide (L≤|fieldValue f tri c-(f[site]?.getD 0)|)))) &&
  (match leaf.winner with
  | none => true
  | some winner => p.sites.contains winner &&
      (List.range p.sites.length).all (fun i =>
        let U:=leaf.upper[i]?.getD 0
        if p.sites[i]?.getD 0 = winner then
          (List.range p.sites.length).all (fun j =>
            decide (i=j) || decide (U+2*leaf.radius<leaf.lower[j]?.getD 0))
        else true))

def covered (leaves : List Leaf) (face : ℕ) (address : List ℕ) : ℕ → Bool
  | 0 => leaves.any (fun l => l.face==face && l.address==address)
  | n+1 => if leaves.any (fun l => l.face==face && l.address==address) then true
      else (List.range 4).all (fun i => covered leaves face (address++[i]) n)

def coverageCheck (m : Mesh) (p : Packet) : Bool :=
  (List.range m.faces.length).all (fun f => covered p.leaves f [] p.depth) &&
  (List.range p.leaves.length).all (fun i =>
    (List.range p.leaves.length).all fun j =>
      let a:=p.leaves[i]?.getD ⟨0,[],none,0,[],[]⟩
      let b:=p.leaves[j]?.getD ⟨0,[],none,0,[],[]⟩
      decide (i=j) || decide (a.face≠b.face) || decide (a.address.take b.address.length≠b.address))

def accepts (m : Mesh) (p : Packet) : Bool :=
  meshCheck m && decide (2≤p.sites.length ∧ p.depth≤8) &&
  decide (p.sites.eraseDups.length=p.sites.length) && p.sites.all (fun s => decide (s<m.vertices)) &&
  p.fields.all (fieldCheck m) && decide (p.paths.length=p.sites.length) &&
  (List.range p.sites.length).all (fun i =>
    let rows:=p.paths[i]?.getD []; let site:=p.sites[i]?.getD 0
    decide (rows.length=m.vertices) && (List.range m.vertices).all (fun v => pathCheck m site v (rows[v]?.getD []))) &&
  p.leaves.all (leafCheck m p) && coverageCheck m p

/-- Accepted packet fields satisfy the native exact gradient checker. -/
theorem accepted_fields (m : Mesh) (p : Packet) (h : accepts m p=true) :
    ∀ f ∈ p.fields, fieldCheck m f=true := by
  simp only [accepts,Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.1.1.1.2

theorem accepted_leaves (m : Mesh) (p : Packet) (h : accepts m p=true) :
    ∀ leaf ∈ p.leaves, leafCheck m p leaf=true := by
  simp only [accepts,Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.2

theorem accepted_coverage (m : Mesh) (p : Packet) (h : accepts m p=true) :
    coverageCheck m p=true := by
  simp only [accepts,Bool.and_eq_true] at h
  exact h.2

theorem accepted_mesh (m : Mesh) (p : Packet) (h : accepts m p=true) :
    meshCheck m=true := by
  simp only [accepts,Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1

theorem checked_gradient (m : Mesh) (field : List ℚ) (h : fieldCheck m field=true)
    (tri : Face) (htri : tri ∈ m.faces) :
    let g:=gram m tri
    let u:=(field[tri.2.1]?.getD 0)-(field[tri.1]?.getD 0)
    let v:=(field[tri.2.2]?.getD 0)-(field[tri.1]?.getD 0)
    g.2.2*u^2-2*g.2.1*u*v+g.1*v^2 ≤ g.1*g.2.2-g.2.1^2 := by
  simp only [fieldCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true (List.all_eq_true.mp h.2 tri htri)

end PerfectPower.RationalVoronoiPacket
