# FOL tableaux solver

tableaux is a mix project folder. It includes a tableaux based solver for propositional logic + predicates but no quantifiers (so far!) and a TPTP parser for fof and cnf based on yecc and leex.
The tableaux file includes two modules, the solver itself and a helper for e.g. timed execution of the solver.

###### to run the parser/solver:
in the mix project folder run:
```
    iex -S mix
```
Then in the elixir command line run:
```
    x = Parser.parse_TPTP_from_file(<filepath>)
    Tableaux.proof(x)
```
