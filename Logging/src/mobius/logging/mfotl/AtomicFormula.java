package mobius.logging.mfotl;

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
    private static final Logger my_logger = new Logger(false);
    
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
    private Set<int[]> findResultSet(Set<int[]> a_set) {
        for (int[] a_i : a_set) {
            for (int i = 0; i < a_i.length; i++) {
                
            }
        }
        return null;
    }
    
    // Public Methods
    //@ public normal_behavior
    //@   assignable \nothing;
    //@   ensures \result == my_predicate.getSymbol();
    public /*@ pure @*/ String getName() {
        return my_predicate.getSymbol();
    }
    
    //@ assignable my_value;
    // TODO change to set based evaluation, 
    public Set evaluate(final /*@ non_null @*/ Structure a_structure,
            final /*@ non_null @*/ Valuation a_valuation) {
        int[] temp_val = new int[my_variables.size()];
        
        for (int i = 0; i < my_variables.size(); i++) {
            temp_val[i] = a_valuation.evaluateVar(my_variables.get(i).getName());
            my_variables.get(i).setValue(temp_val[i]);
        }
        
        Set<int[]> set_real = a_structure.getRelationAssign(my_predicate.getSymbol()); 
        
        Set<int[]> set_result = findResultSet(set_real);
        
        return null;
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
}