import MachCSL.Logic.HeapProofs
import MachCSL.Logic.HeapRegistry

namespace MachCSL.Logic.Heap

theorem registryHeapSpec : HeapSpec registryCapacity := heapSpec registryCapacity

end MachCSL.Logic.Heap
