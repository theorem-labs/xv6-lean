import MachCSL.Machine.PmaClassDefs

namespace MachCSL.Machine.PmaClass
open LeanPaperStock.Functions

structure Spec : Prop where
  ram_match : ∀ address width, access .ram address width →
    matching_pma_region pmaBoot (.Physaddr address) width = some ramRegion
  io_match : ∀ address width, access .io address width →
    matching_pma_region pmaBoot (.Physaddr address) width = some ioRegion
  ram_grants : grants .ram ramRegion
  io_grants : grants .io ioRegion
  boot : allowsAll pmaBoot
  ram : ∀ regions, allowsAll regions → allowsClass .ram regions
  io : ∀ regions, allowsAll regions → allowsClass .io regions

end MachCSL.Machine.PmaClass
