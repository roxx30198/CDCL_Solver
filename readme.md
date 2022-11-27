# SAT solver using CDCL algorithm 
This SAT solver is based on CDCL algorithm .
To read more on CDCL [Conflict Driven Clause Learning (CDCL)](https://en.wikipedia.org/wiki/Conflict-Driven_Clause_Learning).

# Running the solver

## Requirements
This code is implemented in python 3.0
* Compiling the code and Running

**Make sure you are in CDCL directory**

```
$ python3 .\cdcl_solver.py cnf.conf

```
### Input format
The input is a SAT formula is DIMACS format. A detailed description can be found [here](http://www.satcompetition.org/2009/format-benchmarks2009.html).

### Output format
* If the formula is satisfiable,the output is `SAT` followed by the satisfying assignents of the literals. `Notice:` The output is in dimacs form 
 
* If the formula is unsatisfiable, the output consists of a single word, `UNSAT`.
