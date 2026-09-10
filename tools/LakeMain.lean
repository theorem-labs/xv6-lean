import Lake.DSL
import Lake.CLI.Main

-- Run Lake under `lean -jN --run` so Lake itself also respects the thread cap.
def main (args : List String) : IO UInt32 := Lake.cli args
