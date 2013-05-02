package mobius.logging.mfotl;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 * <code>AtomicFormula</code>
 */

public final /*@ immutable pure @*/ class AtomicFormula extends Formula {
    // Attributes
    //@ public invariant
    private final Predicate my_predicate;
    private final List<String> my_variables;
    private final List<String> my_free_variable;
    private boolean my_boolean;
    private static final Logger my_logger = new Logger(true);
    
    // Constructors
    //@ public normal_behavior
    //@   requires \not_specified;
    //@   assignable my_predicate;
    //@   assignable my_variable;
    //@   ensures \not_specified;
    public AtomicFormula(final String[] a_var, final String a_operator, 
            final Signature the_signature) {
        super();
        
        my_logger.info("Build atomic formula Constructor 0 -->");
        my_logger.debug(a_var);
        my_logger.debug(a_operator);
        
        my_variables = new LinkedList();
        my_free_variable = new LinkedList();
        
        for (int i = 0; i < a_var.length; i++) {
            my_variables.add(a_var[i]);
        }
        
        my_predicate = new Predicate(a_operator, a_var.length);        
        if (! the_signature.contains(my_predicate)) {
            my_logger.fatal("Invalid Relation!");
        }
        
        this.initFreeVar();
    }
    
    //@ assignable my_variable;
    //@ assignable my_predicate;
    public AtomicFormula(final /*@ non_null @*/ String[] a_formula, final /*@ non_null @*/ Signature a_signature) {
        super();
        
        my_logger.info("Build atomic formula Constructor 1 -->");        
        my_logger.debug(a_formula);
        
        my_variables = new LinkedList();
        my_free_variable = new LinkedList();

        if (a_formula.length == 1) {
            if (a_formula[0].equals("True")) {
                my_boolean = true;
            } else if (a_formula[0].equals("False")) {
                my_boolean = false;
            }
            my_logger.warning("Boolean Constant " + a_formula[0]);
            my_predicate = null;
        } else if (a_formula[1].equals("=") || a_formula[1].equals("<")) { // Handle = and < later
            my_variables.add(a_formula[0]);
            my_variables.add(a_formula[2]);
            my_predicate = new Predicate(a_formula[1], 2);
        } else {
            String[] temp_var = new String[(a_formula.length-2)/2];
            for (int i = 0; i < temp_var.length; i++) {
                temp_var[i] = a_formula[(i+1)*2];
            }
            // my variables also contain constant
            for (int i = 0; i < temp_var.length; i++) {
                my_variables.add(temp_var[i]);
            }
            
            my_predicate = new Predicate(a_formula[0], temp_var.length);
            if (!a_signature.contains(my_predicate)) {
                my_logger.fatal("Invalid Relation!");
            }
        }
        
        this.initFreeVar();
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
    
    // Private Method
    //@ public normal_behavior
    //@   assignable \nothing;
    private /*@ pure @*/ Set<VarAssigns> findValuationSet(final Set<int[]> a_set) {
        final Set<VarAssigns> temp_set = new HashSet();
        
        if (a_set == null) {
            return temp_set;
        }
        
        for (int[] a_i : a_set) {
            final VarAssigns temp_va = new VarAssigns();

            int int_i;
            for (int_i = 0; int_i < a_i.length; int_i++) {
                final String var_name = my_variables.get(int_i);
                try {
                    final int temp_int = Integer.parseInt(var_name);
                    my_logger.debug("Evaluate Constant: " + var_name + " to " + temp_int);
                    if (temp_int != a_i[int_i]) {
                        break;
                    }
                } catch(NumberFormatException nfe) {
                    temp_va.add(var_name, a_i[int_i]);
                    my_logger.debug("Evaluate Var: " + var_name + " to " + a_i[int_i]);
                }
            }
            
            if (int_i == a_i.length) {
                temp_set.add(temp_va);
            }
        }
        
        return temp_set;
    }
    
    // Public Methods
    //@ public normal_behavior
    //@   assignable \nothing;
    //@   ensures \result == my_predicate.getSymbol();
    public /*@ pure @*/ String getName() {
        return my_predicate.getSymbol();
    }
    
    //@ assignable my_value;
    public Evaluation evaluate(final Structure a_structure) {
        final Evaluation temp_valuation = new Evaluation(this.my_free_variable);
        if (a_structure == null) {
            my_logger.warning("NULL structure in Atomic Evaluation!");
            temp_valuation.setState(0);
            return temp_valuation;
        }
        // Nullary true case
        if (a_structure.containsNullaryRelation(my_predicate.getSymbol())) {
            temp_valuation.setState(1);
            return temp_valuation;
        }
        // other cases
        final Set<int[]> set_real = a_structure.getRelationAssign(my_predicate.getSymbol()); 
        final int[] temp_constant = new int[this.my_variables.size()];
        int temp_i;
        for (temp_i = 0; temp_i < this.my_variables.size(); temp_i++) {
            final String var_name = my_variables.get(temp_i);
            try {
                final int temp_int = Integer.parseInt(var_name);
                temp_constant[temp_i] = temp_int;
                my_logger.debug("Evaluate Constant: " + var_name + " to " + temp_int);
            } catch(NumberFormatException nfe) { // variable exists
                final Set<VarAssigns> set_result = findValuationSet(set_real);
                if (set_result.isEmpty()) {
                    temp_valuation.setState(0);
                } else {
                    temp_valuation.addVarAssign(set_result);    
                }
                return temp_valuation;
            }
        }
        
        if (temp_i == this.my_variables.size()) { 
            if (setContains(set_real, temp_constant)) { // no variables
                temp_valuation.setState(1); // valid atomic formula
            } else {
                temp_valuation.setState(0); // unsatisfiable atomic formula
            }
        } else {
            my_logger.fatal("Error while evaluate atomic formula!");
        }
        
        return temp_valuation;
    }
    
    //@ pure
    public int getVariableSize() {
        return this.my_variables.size();
    }
    
    //@ pure
    public Set<String> getFreeVariable() {
        return new HashSet(this.my_free_variable);
    }
    
    //@ public normal_behavior
    //@   assignable \nothing;
    public /*@ pure @*/ String toString() {
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