#!/usr/bin/env python3
"""
Prolog Interpreter for handling the specific nested list syntax format.
Designed to process the only_ssi_test predicate with family database.
"""

import copy
from typing import List, Dict, Any, Tuple, Optional, Union

class PrologInterpreter:
    def __init__(self):
        self.facts = []
        self.rules = []
        self.variables = {}
        
    def is_variable(self, term):
        """Check if a term is a variable (format: [v, variable_name])"""
        return (isinstance(term, list) and len(term) == 2 and term[0] == 'v')
    
    def is_atom(self, term):
        """Check if a term is an atom (not a list or variable)"""
        return not isinstance(term, list)
    
    def get_variable_name(self, var_term):
        """Extract variable name from [v, variable_name]"""
        if self.is_variable(var_term):
            return var_term[1]
        return None
    
    def substitute_variables(self, term, bindings):
        """Substitute variables in a term with their bindings"""
        if self.is_variable(term):
            var_name = self.get_variable_name(term)
            if var_name in bindings:
                return bindings[var_name]
            return term
        elif isinstance(term, list):
            return [self.substitute_variables(subterm, bindings) for subterm in term]
        else:
            return term
    
    def unify(self, term1, term2, bindings=None):
        """Unification algorithm to match terms"""
        if bindings is None:
            bindings = {}
        
        # Handle variables
        if self.is_variable(term1):
            var_name = self.get_variable_name(term1)
            if var_name in bindings:
                return self.unify(bindings[var_name], term2, bindings)
            else:
                bindings[var_name] = term2
                return bindings
        
        if self.is_variable(term2):
            var_name = self.get_variable_name(term2)
            if var_name in bindings:
                return self.unify(term1, bindings[var_name], bindings)
            else:
                bindings[var_name] = term1
                return bindings
        
        # Handle atoms
        if self.is_atom(term1) and self.is_atom(term2):
            if term1 == term2:
                return bindings
            else:
                return None
        
        # Handle lists
        if isinstance(term1, list) and isinstance(term2, list):
            if len(term1) != len(term2):
                return None
            
            for i in range(len(term1)):
                bindings = self.unify(term1[i], term2[i], bindings)
                if bindings is None:
                    return None
            
            return bindings
        
        return None
    
    def parse_knowledge_base(self, kb):
        """Parse the knowledge base into facts and rules"""
        self.facts = []
        self.rules = []
        
        for item in kb:
            if len(item) >= 3 and item[2] == ":-":
                # This is a rule: head :- body
                rule = {
                    'head': item[:2],
                    'body': item[3] if len(item) > 3 else []
                }
                self.rules.append(rule)
            else:
                # This is a fact
                self.facts.append(item)
    
    def solve_goal(self, goal, bindings=None):
        """Solve a goal using facts and rules"""
        if bindings is None:
            bindings = {}
        
        solutions = []
        
        # Try to match against facts
        for fact in self.facts:
            result_bindings = self.unify(goal, fact, copy.deepcopy(bindings))
            if result_bindings is not None:
                solutions.append(result_bindings)
        
        # Try to match against rules
        for rule in self.rules:
            # Rename variables in the rule to avoid conflicts
            rule_head = self.rename_variables(rule['head'])
            rule_body = self.rename_variables(rule['body'])
            
            result_bindings = self.unify(goal, rule_head, copy.deepcopy(bindings))
            if result_bindings is not None:
                # Solve the body of the rule
                body_solutions = self.solve_body(rule_body, result_bindings)
                solutions.extend(body_solutions)
        
        return solutions
    
    def rename_variables(self, term, suffix=None):
        """Rename variables to avoid conflicts"""
        if suffix is None:
            import random
            suffix = str(random.randint(1000, 9999))
        
        if self.is_variable(term):
            var_name = self.get_variable_name(term)
            return [term[0], var_name + "_" + suffix]
        elif isinstance(term, list):
            return [self.rename_variables(subterm, suffix) for subterm in term]
        else:
            return term
    
    def solve_body(self, body, bindings):
        """Solve the body of a rule (conjunction of goals)"""
        if not body:
            return [bindings]
        
        solutions = []
        
        if isinstance(body, list) and len(body) > 0:
            first_goal = body[0]
            rest_goals = body[1:]
            
            # Handle built-in predicates
            if self.is_builtin_predicate(first_goal):
                builtin_solutions = self.solve_builtin(first_goal, bindings)
                for solution in builtin_solutions:
                    if rest_goals:
                        rest_solutions = self.solve_body(rest_goals, solution)
                        solutions.extend(rest_solutions)
                    else:
                        solutions.append(solution)
            else:
                # Regular goal
                goal_solutions = self.solve_goal(first_goal, bindings)
                for solution in goal_solutions:
                    if rest_goals:
                        rest_solutions = self.solve_body(rest_goals, solution)
                        solutions.extend(rest_solutions)
                    else:
                        solutions.append(solution)
        
        return solutions
    
    def is_builtin_predicate(self, goal):
        """Check if a goal is a built-in predicate"""
        if isinstance(goal, list) and len(goal) >= 2:
            if isinstance(goal[0], list) and len(goal[0]) == 2 and goal[0][0] == 'n':
                pred_name = goal[0][1]
                return pred_name in ['findall', 'not', '=', '>', '<', 'writeln']
        return False
    
    def solve_builtin(self, goal, bindings):
        """Solve built-in predicates"""
        if not isinstance(goal, list) or len(goal) < 2:
            return []
        
        pred_name = goal[0][1] if isinstance(goal[0], list) and goal[0][0] == 'n' else None
        
        if pred_name == 'findall':
            return self.solve_findall(goal[1], bindings)
        elif pred_name == '=':
            return self.solve_equals(goal[1], bindings)
        elif pred_name == '>':
            return self.solve_greater(goal[1], bindings)
        elif pred_name == 'not':
            return self.solve_not(goal[1], bindings)
        elif pred_name == 'writeln':
            return self.solve_writeln(goal[1], bindings)
        
        return []
    
    def solve_findall(self, args, bindings):
        """Implement findall/3 predicate"""
        if len(args) != 3:
            return []
        
        template = args[0]
        goal_list = args[1]
        result_var = args[2]
        
        solutions = []
        
        # Solve the goal list
        if isinstance(goal_list, list):
            goal_solutions = self.solve_body(goal_list, copy.deepcopy(bindings))
            
            results = []
            for solution in goal_solutions:
                instantiated_template = self.substitute_variables(template, solution)
                results.append(instantiated_template)
            
            # Unify the result with the result variable
            if self.is_variable(result_var):
                var_name = self.get_variable_name(result_var)
                new_bindings = copy.deepcopy(bindings)
                new_bindings[var_name] = results
                solutions.append(new_bindings)
            else:
                # Result var is not a variable, try to unify directly
                result_bindings = self.unify(result_var, results, copy.deepcopy(bindings))
                if result_bindings is not None:
                    solutions.append(result_bindings)
        
        return solutions
    
    def solve_equals(self, args, bindings):
        """Implement =/2 predicate"""
        if len(args) != 2:
            return []
        
        result_bindings = self.unify(args[0], args[1], copy.deepcopy(bindings))
        if result_bindings is not None:
            return [result_bindings]
        return []
    
    def solve_greater(self, args, bindings):
        """Implement >/2 predicate"""
        if len(args) != 2:
            return []
        
        left = self.substitute_variables(args[0], bindings)
        right = self.substitute_variables(args[1], bindings)
        
        try:
            if isinstance(left, (int, float)) and isinstance(right, (int, float)):
                if left > right:
                    return [bindings]
        except:
            pass
        
        return []
    
    def solve_not(self, args, bindings):
        """Implement not/1 predicate"""
        if len(args) != 1:
            return []
        
        goal = args[0]
        solutions = self.solve_goal(goal, copy.deepcopy(bindings))
        
        if not solutions:  # If goal fails, not succeeds
            return [bindings]
        return []  # If goal succeeds, not fails
    
    def solve_writeln(self, args, bindings):
        """Implement writeln/1 predicate"""
        if len(args) != 1:
            return []
        
        term = self.substitute_variables(args[0], bindings)
        print(term)
        return [bindings]
    
    def resolve_variable_chains(self, term, bindings):
        """Resolve chains of variable bindings to get the final value"""
        if self.is_variable(term):
            var_name = self.get_variable_name(term)
            if var_name in bindings:
                # Follow the chain of variable bindings
                value = bindings[var_name]
                return self.resolve_variable_chains(value, bindings)
            else:
                return term
        elif isinstance(term, list):
            return [self.resolve_variable_chains(subterm, bindings) for subterm in term]
        else:
            return term
    
    def only_ssi_test(self, depth, query, kb, expected_result=None):
        """Main test function that processes the query against the knowledge base"""
        
        # Parse the knowledge base
        self.parse_knowledge_base(kb)
        
        # The query format is [[n,predicate_name],[[v,variable_name]]]
        predicate_info = query[0]  # [n,older_brother]  
        variable_info = query[1]   # [[v,result6]]
        
        # Create the goal: older_brother([[v,result6]])
        goal = [predicate_info, variable_info]
        
        # Solve the goal
        solutions = self.solve_goal(goal)
        
        print(f"DEBUG: Solutions = {solutions}")
        
        # Extract results from the first solution
        results = []
        if solutions:
            solution = solutions[0]
            print(f"DEBUG: First solution = {solution}")
            var_name = variable_info[0][1]  # Extract 'result6' from [[v,result6]]
            print(f"DEBUG: Looking for variable {var_name}")
            if var_name in solution:
                # Resolve any variable chains to get the final value
                raw_value = solution[var_name]
                print(f"DEBUG: Raw value = {raw_value}")
                results = self.resolve_variable_chains(raw_value, solution)
                print(f"DEBUG: Resolved results = {results}")
        
        # Return the result in the expected format
        return [[variable_info[0], results]]


def main():
    """Test the Prolog interpreter with the given example"""
    
    interpreter = PrologInterpreter()
    
    # Test data from the problem statement
    depth = 3
    query = [["n","older_brother"],[["v","result6"]]]
    
    kb = [
        [["n","parent"],["albert", "jim"]],
        [["n","parent"],["albert", "peter"]],
        [["n","parent"],["jim", "brian"]],
        [["n","parent"],["john", "darren"]],
        [["n","parent"],["peter", "lee"]],
        [["n","parent"],["peter", "sandra"]],
        [["n","parent"],["peter", "james"]],
        [["n","parent"],["peter", "kate"]],
        [["n","parent"],["peter", "kyle"]],
        [["n","parent"],["brian", "jenny"]],
        [["n","parent"],["irene", "jim"]],
        [["n","parent"],["irene", "peter"]],
        [["n","parent"],["pat", "brian"]],
        [["n","parent"],["pat", "darren"]],
        [["n","parent"],["amanda", "jenny"]],

        [["n","older_brother"],[["v","c"]],":-",
        [
            [["n","findall"],
            [
                [["v","a"],["v","b"]],

                [
                [["n","siblings"],[["v","a"],["v","b"]]],
                [["n","male"],[["v","a"]]],
                [["n","older"],[["v","a"],["v","b"]]]
                ],

                ["v","c"]
            ]]
        ]],
        [["n","siblings"],[["v","a"],["v","b"]],":-",
        [
            [["n","parent"],[["v","x"],["v","a"]]],
            [["n","parent"],[["v","x"],["v","b"]]],
            [["n","not"],[[["n","="],[["v","a"],["v","b"]]]]]
        ]],
        [["n","male"],["albert"]],
        [["n","male"],["jim"]],
        [["n","male"],["peter"]],
        [["n","male"],["brian"]],
        [["n","male"],["john"]],
        [["n","male"],["darren"]],
        [["n","male"],["james"]],
        [["n","male"],["kyle"]],
        [["n","yearofbirth"],["irene",1923]],
        [["n","yearofbirth"],["pat",1954]],
        [["n","yearofbirth"],["lee",1970]],
        [["n","yearofbirth"],["sandra",1973]],
        [["n","yearofbirth"],["jenny",2004]],
        [["n","yearofbirth"],["amanda",1979]],
        [["n","yearofbirth"],["albert",1926]],
        [["n","yearofbirth"],["jim",1949]],
        [["n","yearofbirth"],["peter",1945]],
        [["n","yearofbirth"],["brian",1974]],
        [["n","yearofbirth"],["john",1955]],
        [["n","yearofbirth"],["darren",1976]],
        [["n","yearofbirth"],["james",1969]],
        [["n","yearofbirth"],["kate",1975]],
        [["n","yearofbirth"],["kyle",1976]],
        [["n","older"],[["v","a"],["v","b"]],":-",
        [
            [["n","yearofbirth"],[["v","a"],["v","y1"]]],
            [["n","yearofbirth"],[["v","b"],["v","y2"]]],
            [["n",">"],[["v","y2"],["v","y1"]]]
        ]],
        [["n","family_test"],":-",
        [
            [["n","older_brother"],[["v","result6"]]],
            [["n","writeln"],[["v","result6"]]]
        ]]
    ]
    
    expected_result = [[["v","result6"],[["peter", "jim"], ["james", "lee"], ["james", "sandra"], ["james", "kate"], ["james", "kyle"], ["peter", "jim"], ["brian", "darren"]]]]
    
    result = interpreter.only_ssi_test(depth, query, kb, expected_result)
    print("Result:", result)
    
    return result


if __name__ == "__main__":
    main()