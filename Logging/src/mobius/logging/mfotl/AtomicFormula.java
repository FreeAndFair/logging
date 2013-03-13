package mobius.logging.mfotl;

import java.util.HashSet;
import java.util.Set;

/*
 * Class Atomic_Formula
 * 
 * for the leave notes of formula
 */

public class AtomicFormula extends Formula {
    // Attributes
    public Predicate my_predicator;
    public boolean my_value = false;
    public Set my_variable = new HashSet();
    
    private final Signature my_signature;
    private static final Logger my_logger = new Logger();
    
    // Constructors
 
    public AtomicFormula(final String[] a_var, final int a_arity, final String a_operator, 
            final Signature a_signature) {
        super();
        
        my_logger.info("\nBuild atomic formula ->");
        my_logger.debug(a_var);
        my_logger.debug(a_operator);
        
        my_signature = a_signature;
        
        my_predicator = new Predicate(a_operator, a_arity, a_var);

        for (String i : a_var) {
            my_variable.add(i);
        }
        
        if ("=".equals(a_operator) || "<".equals(a_operator))
            return;
        
        if (! my_signature.contains(my_predicator)) {
            my_logger.fatal("Invalid Relation!");
        }

    }
    
    public AtomicFormula(final /*@ non_null @*/ String[] a_formula, final /*@ non_null @*/ Signature a_signature) {
        super();
        
        my_logger.info("\nBuild atomic formula ->");        
        my_logger.debug(a_formula);
        
        my_signature = a_signature;
        
        if (a_formula[1].equals("=") || a_formula[1].equals("<")) {
            final String[] temp_var = {a_formula[0], a_formula[2]};
            my_predicator = new Predicate(a_formula[1], 2, temp_var);
            for (String i : temp_var) {
                my_variable.add(i);
            }
        } else {
            String[] temp_var = new String[(a_formula.length-2)/2];
            for (int i = 0; i < temp_var.length; i++) {
                temp_var[i] = a_formula[(i+1)*2];
                for (String j : temp_var) {
                    my_variable.add(j);
                }
            }
            my_predicator = new Predicate(a_formula[0], temp_var.length , temp_var);
            
            if (! my_signature.contains(my_predicator)) {
                my_logger.fatal("Invalid Relation!");
            }
            
        }
    }
    
    // Public Methods
    
    //@ assignable my_value;
    public boolean evaluate(final /*@ non-null @*/ Structure a_structure) {
        my_value = my_predicator.evaluate(a_structure);
        return my_value;
    }
    
    //@ pure
    public String toString() {
        return my_predicator.toString();
    }
}