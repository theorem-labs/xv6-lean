import Xv6.Fs.LinkFamilyDefs
import Xv6.Fs.LinksDefs

/-! Native link-camera supplies from FsDurImg §9a–c. -/
namespace Xv6.Fs.LinkSupply
open DurableNode LinkFamily MachCSL.Logic.FsLink Iris Iris.CMRA Iris.Algebra

noncomputable def authorities (nodes : DurableState.InodeMap) (values : Int → IType) : FamilyRA :=
  bigOpM (M' := FamilyMap) CMRA.op (fun i n => authElem i (multiplicity n) (values i)) nodes

noncomputable def supply (nodes : DurableState.InodeMap) (values : Int → IType) : FamilyRA :=
  bigOpM (M' := FamilyMap) CMRA.op
    (fun i n => toksElem i (reps (multiplicity n) (values i))) nodes

noncomputable def fullMap (nodes : DurableState.InodeMap) (values : Int → IType) : FamilyRA :=
  bigOpM (M' := FamilyMap) CMRA.op (fun i n => fullElem i (multiplicity n) (values i)) nodes

noncomputable def outgoing (nodes : DurableState.InodeMap) (f : Choice) : FamilyRA :=
  bigOpM (M' := FamilyMap) CMRA.op (fun i n => entriesElem i n (choiceTypes f i)) nodes

noncomputable def tokens (values : Int → IType) (tickets : List Int) : FamilyRA :=
  bigOpL CMRA.op (fun _ target => tokElem target (values target)) tickets

end Xv6.Fs.LinkSupply
