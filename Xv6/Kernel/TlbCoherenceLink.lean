import Xv6.Kernel.TlbCoherenceProofs
import Xv6.Kernel.TlbCoherencePlanProofs

namespace Xv6.Kernel.TlbCoherence

theorem nativeSpec : Spec :=
  ⟨index_surjective, all_slots, empty, variant_iff_canon, entry_match, cache_match,
    cache_properties, cache_canon, coherent_canon, fill, fill_self, cache_set_leaf,
    coherent_set_leaf, set_pte_entry, refresh, lookup_hit, lookup_blocked,
    get_pte, get_level, get_ppn⟩

theorem nativePlanSpec : PlanSpec := ⟨lookup_plan, fill_plan, refresh_plan, pbmt_plan⟩

end Xv6.Kernel.TlbCoherence
