# SAT solver based on Conflict Driven clause learning algorithm
# Author - Rohan Jha
# Computer Aided Verification Project
import sys
import random

# Enum to store the values returned by functions
# r_sat: If formula is satisfied
# r_unsat: If the formula is unsatisfied
# r_normal: If the formula is unresolved until now
retval = ["r_sat","r_unsat","r_normal"]
enumerate(retval)

#function to read the input commands and args
def command_reader():
    if len(sys.argv) !=2:
        print("Usage : python cdcl-solver.py cnf.conf ")
        sys.exit()
    
    if sys.argv[1] != 'cnf.conf':
        print("Enter correct input file")
        sys.exit()

command_reader()

# Class containing functions and variables for the CDCL solver

class cdcl_solver:
    literal_antecedent = "" 
    assigned_literals_count = 0
    num_clause = 0
    num_literal = 0
    clauses = []
# Parser function that takes input from the cnf.conf file
# Stores the num_clause and num_literal as well as the clauses in class variables
    def input_parser(self):
        self.clauses = []
        for line in open('cnf.conf'):
            if line.startswith('c'):
                continue
            if line.startswith('p'):
                self.num_literal = line.split(' ')[2]
                self.num_clause = line.split(' ')[3]
                continue

            clause = [int(x) for x in line[:-2].split()]
            self.clauses.append(clause)
        self.num_clause = int(self.num_clause)
        self.num_literal = int(self.num_literal)
        self.literals_state = [-1]*int(self.num_literal) #stores the state of each variable
        self.literal_decision_level = [-1]*int(self.num_literal) #stores the decision level of each variable
        self.literal_antecedent = [-1]*int(self.num_literal) #stores the antecedent of each variable

#  function to perform unit propagation on the formula
#  Args : decision_level - the current decision level at which unit
#  propagation is taking place Return value : Return state denoting the status,
#  where return value,
#  r_normal - unit propagation ended successfully with no
# r_unsat - unit propagation found a conflict
     
    def unit_propagate(self,decision_level):
        self.unit_clause_found = True # Flag to check if unit clause is found
        self.fal_count = 0 # number of false literals in the clause
        self.unset_count = 0 # number of unset literals in the clause
        self.satisfied_flag = False # if the clause is satisfied due to the presence of a true literal
        self.last_unset_literal = -1 # index of an unset literal
        while self.unit_clause_found == True:
            self.unit_clause_found = False
            i_ind = -1
            for i in self.clauses:
                i_ind +=1
                if self.unit_clause_found == True:
                    break
                self.unset_count = 0
                self.fal_count = 0
                self.satisfied_flag = False
                w = 0
                for n in i:
                    w += 1
                    self.literal_index = self.literal_to_variable_index(n)

                    if self.literals_state[self.literal_index] == -1:
                        self.unset_count +=1
                        self.last_unset_literal = w-1
                    elif (self.literals_state[self.literal_index] == 0 and 
                         n > 0) or (self.literals_state[self.literal_index] == 1 and
                         n<0):
                        self.fal_count +=1
                    else:
                        self.satisfied_flag = True
                        break
                if self.satisfied_flag: # if the clause is satisfied, move to the next
                    continue
                if self.unset_count == 1: # if exactly one literal is unset, this clause is unit literal
                    self.assign_literal(i[self.last_unset_literal],decision_level,i_ind)
                    self.unit_clause_found = True
                    break
                elif self.fal_count == len(i):
                    self.kappa_antecedent = i_ind # set the antecedent of kappa to this clause
                    return retval[1]
                
        self.kappa_antecedent = -1
        return retval[2] # return normally      

#  function to assign a value, decision level, and antecedent to a variable
#  Args : var - the one indexed signed form of the variable, where the
#  sign tells the direction of assignment 
#  decision_level - the decision level to assign at 
#  antecedent - the antecedent of the assignment
 
           
    def assign_literal(self, var, dec_level,antecedent):
        literal = self.literal_to_variable_index(var)
        if var > 0:
            var = 1
        else:
            var = 0
        self.literals_state [literal] = var
        self.literal_decision_level[literal] = dec_level
        self.literal_antecedent[literal] = antecedent
        self.literal_frequency[literal] = -1
        self.assigned_literals_count +=1

# function to unassign a variable
# Args : literal_index - the index of the variable to unassign
        
    def unassign_literal(self,literal_index):
        self.literals_state[literal_index] = -1
        self.literal_decision_level[literal_index] = -1
        self.literal_antecedent[literal_index] = -1
        self.literal_frequency[literal_index] = self.original_literal_frequency[literal_index]
        self.assigned_literals_count -=1

# function to convert the one indexed signed form of the literal to the zero index
# index Arguments : var - the one indexed signed form
# Return value : the zero indexed list index

    def literal_to_variable_index(self,var):
        if int(var) > 0:
            return var-1
        else:
            return -var-1
        
# function to resolve a clause with the antecedent of a literal and return the result
# Args : inp_clause - the existing clause 
# lite - the literal whose antecedent must be resolved with 
# Return value : the resultant clause

    def resolve(self,inp_clause : list, lite):
        sec_inp = self.clauses[self.literal_antecedent[lite]]
        inp_clause.extend(sec_inp)
        i = 0
        while i < len(inp_clause):
                if inp_clause[i] == lite+1 or inp_clause[i] == -lite-1:
                    inp_clause.pop(i)
                    i-=1
                else:
                    i+=1

        inp_clause.sort()
        res = [*set(inp_clause)] #extracting unique elements
        return res
    
# function to perform conflict analysis and backtrack
# Arguments : decision_level - the decision level of the conflict
# Return value : the backtracked decision level
       
    def conflict_analysis_and_backtrack(self,decision_level):
        self.learnt_clause = self.clauses[self.kappa_antecedent]
        self.conflict_decision_level = decision_level
        self.this_level_count = 0 
        resolver_literal = 0
        while True:
            self.this_level_count = 0
            for i in range(0,len(self.learnt_clause)):
                self.literal = self.literal_to_variable_index(self.learnt_clause[i])
                if self.literal_decision_level[self.literal] == self.conflict_decision_level:
                    self.this_level_count +=1
                if self.literal_decision_level[self.literal] == self.conflict_decision_level and self.literal_antecedent[self.literal] != -1:
                    resolver_literal = int(self.literal)
            if self.this_level_count == 1:
                break
            
            self.learnt_clause = self.resolve(self.learnt_clause,resolver_literal)
        self.clauses.append(self.learnt_clause)
        for i in range(0,len(self.learnt_clause)):
            lit_index = self.literal_to_variable_index(self.learnt_clause[i])
            if self.learnt_clause[i] > 0:
                update = 1
            else:
                update = -1
            self.literal_polarity[lit_index] +=update
            if self.literal_frequency[lit_index] != -1:
                self.literal_frequency[lit_index]+=1
            self.original_literal_frequency[lit_index] +=1
        self.num_clause += 1
        backtrack_dec_level = 0
        for i in range(0,len(self.learnt_clause)):
            lit_index = self.literal_to_variable_index(self.learnt_clause[i])
            dec_level_here = self.literal_decision_level[lit_index]
            if dec_level_here != self.conflict_decision_level and dec_level_here > backtrack_dec_level:
                backtrack_dec_level = dec_level_here
        for i in range(0,len(self.literals_state)):
            if self.literal_decision_level[i] > backtrack_dec_level:
                self.unassign_literal(i)
        return backtrack_dec_level
    
# function to pick a variable and an assignment to be assigned freely next
# Return value : the one indexed signed form of the variable where the sign
# denotes the direction of the assignment
        
    def pick_branching_variable(self):
        choose_branch = random.randrange(1,11)  # to generate a random integer between 1 and 11, for deciding the mechanism of choosing
        too_many_attempts = False
        attempt_counter = 0
        while too_many_attempts == False:
            if (choose_branch > 4) or (self.assigned_literals_count < int(self.num_literal)//2) or (too_many_attempts):
                self.pick_counter+=1
                if self.pick_counter==20*self.num_literal:
                    for i in range(0,len(self.literals_state)):
                        self.original_literal_frequency[i]/=2
                        if self.literal_frequency[i]!=-1:
                            self.literal_frequency[i]/=2
                    self.pick_counter = 0
                var1 = max(self.literal_frequency)
                var2 = self.literal_frequency.index(var1)
                if(self.literal_polarity[var2]) >=0:
                    return var2+1
                return -var2-1
            else:
                for attempt_counter in range(0,10*int(self.num_literal)):
                    variable = random.randrange(0,int(self.num_literal)-1)
                    if self.literal_frequency[variable]!=1:
                        if self.literal_polarity[variable]>=0:
                            return variable+1
                        return -variable-1
                    attempt_counter +=1
                    too_many_attempts = True

# function to check if all variables have been assigned so far
# Return value : true, if yes, false, if no

    def all_variables_assigned(self):
        if int(self.num_literal) == self.assigned_literals_count:
            return True
        else:
            return False
        
# function to display the result of the solver
# Arguments : result_status - the status that CDCL returned
           
    def show_result(self, result_status):
        if result_status == retval[0]:
            print("SAT")
            for i in range(0,len(self.literals_state)):
                if i!=0:
                    pass
                if self.literals_state[i]!=-1:
                    print(pow(-1,(self.literals_state[i]+1)) *(i+1),end=" ")
                else:
                    print(i+1)
        else:
            print("UNSAT")

# Function to intialize the solver  
            
    def initialize(self):
        self.input_parser()
        self.kappa_antecedent = -1
        self.pick_counter = 0
        self.already_unsatisfied = False
        self.literal_frequency = [0]* int(self.num_literal)
        self.literal_polarity = [0]*int(self.num_literal)
        k = 0
        for n in self.clauses:
            self.literal_count_in_clause = 0
            for literal in n:
                if literal > 0 :
                    self.literal_frequency[literal-1] += 1
                    self.literal_polarity[literal-1] += 1
                elif literal < 0 :
                    self.literal_frequency[-1-literal] += 1
                    self.literal_polarity[-1-literal] -= 1
                else:
                    if self.literal_count_in_clause ==0:
                        self.already_unsatisfied = True
                    break
                self.literal_count_in_clause +=1
        self.original_literal_frequency = self.literal_frequency

# function to implement the Conflict Driven Clause Learning algorithm
# Return value : 
# r_sat: if the formula is satisfiable
# r_unsat: if the formula is not satisfiable

    def cdcl(self):
        self.decision_level = 0
        if self.already_unsatisfied :
            return retval[1]
        self.unit_propagate_result = self.unit_propagate(self.decision_level)
        if self.unit_propagate_result == retval[1]:
            return self.unit_propagate_result
        self.picked_variable = self.pick_branching_variable()   

        while self.all_variables_assigned() != True:
            self.picked_variable = self.pick_branching_variable()
            self.decision_level+=1
            self.assign_literal(self.picked_variable,self.decision_level,-1)
            while True:
                self.unit_propagate_result = self.unit_propagate(self.decision_level)
                if self.unit_propagate_result == retval[1]:
                    if self.decision_level == 0 :
                        return self.unit_propagate_result
                    self.decision_level = self.conflict_analysis_and_backtrack(self.decision_level)
                else:
                    break
        return retval[0]      

# Calling the cdcl and show_result functions from solve()            
    def solve(self):
        result_stat = self.cdcl()
        self.show_result(result_stat)


# Creating an instance of the solver class
c1 = cdcl_solver()

# Intializing and calling the solve function
c1.initialize()
c1.solve()