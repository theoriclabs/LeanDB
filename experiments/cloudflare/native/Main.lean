import CfNative
import LeanDb.Http

def main (args : List String) : IO UInt32 := LeanDb.Cli.run CfNative.base args
