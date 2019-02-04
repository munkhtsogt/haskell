# Denotational Semantics

Environment
===========
	- The Glorious Glasgow Haskell Compilation System, version 7.10.3
	- Sublime Text Editor
	- Command: "ghc --make Tests.hs & ./Tests"
 
I added some additional features (language extensions) to the basic definitions in the continuation semantic model (Impc). I used same test cases and added own test cases. In addition I added Goto sequencer and Leave methods.

Following features are added:
	- Static Binding
	- Single Parameter
	- Goto
	- Leave
	- Loop
	- Run (Read)
	- Draw

Result
======
"------ APL:: DSem_impc"
":---: expressions  [ 2, 1+2, 1+2*3 ]"
Output (IntValue 2,Halt)
Output (IntValue 3,Halt)
Output (IntValue 7,Halt)
":---: declaration    {const x = 2}"
Halt
":---: {result = input}  [1, 2]"
IntValue 1
IntValue 2
":---: {result = input+1}  [2, 3]"
IntValue 2
IntValue 3
":---: Simple Program.2  -> [1]"
Halt
Output (IntValue 1,Halt)
IntValue 0
":---: Simple Program.3  -> [3,1]"
Output (IntValue 3,Output (IntValue 1,Halt))
":---: Simple Program.4  -> [0,6, Halt]"
Output (IntValue 0,Output (IntValue 6,Halt))
Output (IntValue 3,Halt)
":--: Simple Program.5 (Goto)  -> [5, Halt]"
Output (IntValue 5,Halt)
":--: Simple Program.6 (Leave)  -> [1, Halt]"
Output (IntValue 1,Halt)
