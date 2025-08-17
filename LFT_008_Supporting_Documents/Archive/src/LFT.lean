import Mathlib# 2) Minimal source so build has a target
mkdir src -ea 0
@'
import Mathlib

def hello : String := "LFT + mathlib 4.21.0"
#eval IO.println hello
