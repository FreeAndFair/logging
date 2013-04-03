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
    private final List<Variable> my_variables;
    private static final Logger my_logger = new Logger(true);
    
    // Constructors
    //@ public normal_behavior
    //@   requires \not_specified;
    //@   assignable my_predicate;
    //@   assignable my_variable;
    //@   ensures \not_specified;
    public AtomicFormula(final String[] a_var, final int a_arity, final String a_operator, 
            final Signature the_signature) {
        super();
        
        my_logger.info("\nBuild atomic formula ->");
        my_logger.debug(a_var);
        my_logger.debug(a_operator);
        
        my_variables = new LinkedList();
        
        for (int i = 0; i < a_arity; i++) {
            my_variables.add(new Variable(a_var[i]));
        }
        
        my_predicate = new Predicate(a_operator, a_arity);        
        if (! the_signature.contains(my_predicate)) {
            my_logger.fatal("Invalid Relation!");
        }
    }
    
    //@ assignable my_variable;
    //@ assignable my_predicate;
    public AtomicFormula(final /*@ non_null @*/ String[] a_formula, final /*@ non_null @*/ Signature a_signature) {
        super();
        
        my_logger.info("\nBuild atomic formula ->");        
        my_logger.debug(a_formula);
        my_variables = new LinkedList();
        
        if (a_formula[1].equals("=") || a_formula[1].equals("<")) {
            my_variables.add(new Variable(a_formula[0]));
            my_variables.add(new Variable(a_formula[2]));
            my_predicate = new Predicate(a_formula[1], 2);
        } else {
            String[] temp_var = new String[(a_formula.length-2)/2];
            for (int i = 0; i < temp_var.length; i++) {
                temp_var[i] = a_formula[(i+1)*2];
            }
            // my variables also contain constant
            for (int i = 0; i < temp_var.length; i++) {
                my_variables.add(new Variable(temp_var[i]));
            }
            
            my_predicate = new Predicate(a_formula[0], temp_var.length);
            
            if (! a_signature.contains(my_predicate)) {
                my_logger.fatal("Invalid Relation!");
            }
        }
    }
    
    // Private Method
    //@ public normal_behavior
    //@   assignable \nothing;
    private /*@ pure @*/ Set<List> findValuationSet(final Set<int[]> a_set) {
        final Set<List> temp_set = new HashSet();

        for (int[] a_i : a_set) {
            final List<VariableAssign> temp_l = new LinkedList();
            for (int i = 0; i < a_i.length; i++) {
                final String var_name = my_variables.get(i).getName();
                try {
                    final int temp_int = Integer.parseInt(var_name);
                    my_logger.debug("Evaluate Constant: " + var_name + " to " + temp_int);
                    if (temp_int != a_i[i]) {
                        break;
                    }
                }
                catch(NumberFormatException nfe) {
                    temp_l.add(new VariableAssign(var_name, a_i[i]));
                    my_logger.debug("Evaluate Var: " + var_name + " to " + a_i[i]);
                }
                
                if (i == a_i.length - 1) {
                    temp_set.add(temp_l);
                }
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
    public Valuation evaluate(final Structure a_structure) {
        final Valuation temp_valuation = new Valuation();
        final Set<int[]> set_real = a_structure.getRelationAssign(my_predicate.getSymbol()); 
        
        int[] temp_constant = new int[this.my_variables.size()];
        int temp_i;
        for (temp_i = 0; temp_i < this.my_variables.size(); temp_i++) {
            final String var_name = my_variables.get(temp_i).getName();
            try {
                final int temp_int = Integer.parseInt(var_name);
                temp_constant[temp_i] = temp_int;
                my_logger.debug("Evaluate Constant: " + var_name + " to " + temp_int);
            }
            catch(NumberFormatException nfe) {
                final Set<List> set_result = findValuationSet(set_real);
                temp_valuation.setTruth(!set_result.isEmpty());
                temp_valuation.addVarAssign(set_result);
                return temp_valuation;
            }
        }
        
        if (temp_i == this.my_variables.size()) {
            temp_valuation.setTruth(setContains(set_real, temp_constant));
        } else {
            temp_valuation.setTruth(false);
        }
        
        return temp_valuation;
    }
    
    public /*@ pure @*/ Variable getVariable(final int a_pos) {
        if (a_pos < this.my_variables.size()) {
            return this.my_variables.get(a_pos);
        } else {
            return null;
        }
    }
    
    public /*@ pure @*/ int getVariableSize() {
        return this.my_variables.size();
    }
    
    //@ public normal_behavior
    //@   assignable \nothing;
    public /*@ pure @*/ String toString() {
        String temp_string = my_predicate.toString();
        if (!my_variables.isEmpty()) {
            temp_string = temp_string.concat("(" + my_variables.get(0).getName());
            for (int i = 1; i < my_variables.size(); i++) {
                temp_string = temp_string.concat("," + my_variables.get(i).getName());
            }
            temp_string = temp_string.concat(")");
        }
        
        return temp_string;
    }
    
    private boolean setContains(final Set<int[]> a_set, final int[] a_array) {
        for (int[] temp_i : a_set) {
            if (Arrays.equals(temp_i, a_array)) {
                return true;
            }
        }
        return false;
    }
}