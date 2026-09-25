import VersoManual
import LeanHoas

open Verso.Genre Manual

def main := manualMain (%doc LeanHoas) (config := { htmlDepth := 1 })
