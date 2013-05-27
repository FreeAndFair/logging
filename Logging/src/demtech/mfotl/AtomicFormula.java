package demtech.mfotl;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public final /*@ immutable pure @*/ class AtomicFormula extends Formula {
    // Attributes
    //@ public invariant
    private final Predicate my_predicate;
    private final List<String> my_variables = new LinkedList();
    private final List<String> my_free_variable = new LinkedList();
    private static final Logger my_logger = new Logger(true);
    
    // Constructors
    //@ public normal_behavior
    //@   requires \not_specified;
    //@   assignable my_predicate;
    //@   assignable my_variables;
    //@   ensures \not_specified;
    public AtomicFormula(final String[] a_vars, final String a_operator, final Signature the_signature) {
        super();
        
        my_logger.info("Build atomic formula with Constructor 0 -->");
        my_logger.debug(a_vars);
        my_logger.debug(a_operator);
        
        my_variables.addAll(Arrays.asList(a_vars));
        my_predicate = new Predicate(a_operator, a_vars.length);
        
        if (!the_signature.contains(my_predicate)) {
            my_logger.fatal("Invalid Relation!");
        }
        
        this.initFreeVar();
    }
    
    //@ assignable my_variable;
    //@ assignable my_predicate;
    public AtomicFormula(final String[] a_formula, final Signature a_signature) {
        super();
        
        my_logger.info("Build atomic formula Constructor 1 -->");        
        my_logger.debug(a_formula);
        
        if (a_formula.length == 1) {
            my_logger.warning("Nullary Predicate: " + a_formula[0]);
            my_predicate = new Predicate(a_formula[0], 0);
        } else {
            final String[] temp_var = new String[(a_formula.length-2)/2];
            for (int i = 0; i < temp_var.length; i++) {
                temp_var[i] = a_formula[(i+1)*2];
            }

            my_variables.addAll(Arrays.asList(temp_var));
            my_predicate = new Predicate(a_formula[0], temp_var.length);
            
            this.initFreeVar();
        }
        
        if (!a_signature.contains(my_predicate)) {
            my_logger.fatal("Invalid Relation!");
        }
    }


    // Public Methods
    //@ public normal_behavior
    //@   assignable \nothing;
    //@   ensures \result == my_predicate.getSymbol();
    public /*@ pure @*/ String getName() {
        return my_predicate.getName();
    }
    
    //@ pure
    public Evaluation evaluate(final Structure a_structure) {
        final Evaluation temp_valuation = new Evaluation(this.my_free_variable);
        
        // Null-ary predicate
        if (my_predicate.getArity() == 0) {
            if (a_structure.containsNullaryRelation(my_predicate.getName())) {
                temp_valuation.setState(1);
            } else {
                temp_valuation.setState(0);
            }
            return temp_valuation;
        }
        
        // Other cases
        final Set<int[]> set_real = a_structure.getRelationAssign(my_predicate.getName()); 
        
        if (set_real == null) {
            temp_valuation.setState(0);
            return temp_valuation;
        }
        
        if (!my_free_variable.isEmpty()) {
            final Set<VarAssigns> set_result = findValuationSet(set_real);
            if (set_result.isEmpty()) {
                temp_valuation.setState(0);
            } else {
                temp_valuation.addVarAssign(set_result);    
            }
            return temp_valuation;
        }
        
        final int[] temp_constant = new int[this.my_variables.size()];        
        for (int i = 0; i < this.my_variables.size(); i++) {
            try {
                final int temp_int = Integer.parseInt(my_variables.get(i));
                temp_constant[i] = temp_int;
                my_logger.debug("Evaluate Constant: " + my_variables.get(i) + " to " + temp_int);
            } catch(NumberFormatException nfe) {
                my_logger.fatal("Error while evaluate atomic formula!");
            }
        }
        
        if (setContains(set_real, temp_constant)) { // no variables
            temp_valuation.setState(1); // valid atomic formula
        } else {
            temp_valuation.setState(0); // unsatisfiable atomic formula
        }
        
        return temp_valuation;
    }
    
    //@ pure
    public Set<String> getFreeVariable() {
        return new HashSet(this.my_free_variable);
    }
    
    //@ public normal_behavior
    //@   assignable \nothing;
    //@ pure
    public String toString() {
        String temp_string = my_predicate.toString();
        if (!my_variables.isEmpty()) {
            temp_string = temp_string.concat("(" + my_variables.get(0));
            for (int i = 1; i < my_variables.size(); i++) {
                temp_string = temp_string.concat("," + my_variables.get(i));
            }
            temp_string = temp_string.concat(")");
        }
        
        return temp_string;
    }

    // Private Methods
    
    //@ public normal_behavior
    //@   assignable \nothing;
    private /*@ pure @*/ Set<VarAssigns> findValuationSet(final Set<int[]> a_set) {
        final Set<VarAssigns> temp_set = new HashSet();
        
        for (int[] a_i : a_set) {
            final VarAssigns temp_va = new VarAssigns();

            int int_i;
            for (int_i = 0; int_i < a_i.length; int_i++) {
                final String var_name = my_variables.get(int_i);
                try {
                    final int temp_int = Integer.parseInt(var_name);
                    if (temp_int != a_i[int_i]) {
                        break;
                    }
                    my_logger.debug("Evaluate Constant: " + var_name + " to " + temp_int);
                } catch(NumberFormatException nfe) {
                    temp_va.add(var_name, a_i[int_i]);
                    my_logger.debug("Evaluate Variable: " + var_name + " to " + a_i[int_i]);
                }
            }
            
            if (int_i == a_i.length) {
                temp_set.add(temp_va);
            }
        }
        
        return temp_set;
    }

    private void initFreeVar() {
        for (int i = 0; i < my_variables.size(); i++) {
            try {
                Integer.parseInt(my_variables.get(i));
                my_logger.debug("Constant Var: " + my_variables.get(i));
            } catch(NumberFormatException nfe) {
                my_free_variable.add(my_variables.get(i));
                my_logger.debug("Free Var: " + my_variables.get(i));
            }
        }
    }
    
    //@ pure
    private boolean setContains(final Set<int[]> a_set, final int[] a_array) {
        if (a_set == null || a_array == null) {
            return false;
        }
        for (int[] temp_i : a_set) {
            if (Arrays.equals(temp_i, a_array)) {
                return true;
            }
        }
        return false;
    }
}