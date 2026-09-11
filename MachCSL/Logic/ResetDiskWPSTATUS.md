# Reset-disk worker feasibility rule

`JalDevices.DiskReset` says the actual Virtio state is the source reset of some
previous device. The previous disk and capacity remain arbitrary. Boot facts
establish it, and every UART actor step preserves it.

The actual disk actor has seven arms. At reset, queue liveness excludes request,
capture and pop; an empty cache excludes draining; disabled queue liveness
excludes malformed-chain wild writes; a cleared ISR excludes interrupt latching.
`disk_step_idle` and `disk_thread_idle` prove the resulting exact self-loop,
including no memory write set, unchanged log and no forks. No transition was
removed or modified to obtain this result.

`ResetDiskWP.wp_reset_disk` uses the actual generation certificate and Virtio
client half. In a live generation, native authority agreement establishes the
actual reset state. In a dead generation, the source corpse arm applies. The
guarded native WP retains the full fixed state/trace and its client half through
every silent step. The rule works for any postcondition of the empty value type.
The final registry wrapper supplies all concrete capacities.

This specialization is for the first machine-code feasibility image, which
never configures the device. It is not the production active disk-driver WP,
does not justify arbitrary DMA, and establishes no whole-system adequacy alone.
The proof compiles through the actual machine and native Iris dependencies.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
