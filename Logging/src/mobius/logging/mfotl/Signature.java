package mobius.logging.mfotl;

import java.util.Set;
import java.util.HashSet;


public class Signature {
    // Attributes
    final private Set<Predicate> my_predicate;
    
    // Constructor
    public Signature() {
        my_predicate = new HashSet();
    }
    
    // Public Methods
    public void addPredicate(final Predicate a_predicate) {
        my_predicate.add(a_predicate);
    }
    
    public /*@ pure @*/ boolean contains(final String a_name, final int a_arity) {
        boolean temp_result = false;
        for (Predicate i : my_predicate) {
            if (a_name.equals(i.getSymbol()) && (i.getArity() == a_arity)) {
                temp_result = true;
                break;
            }
        }
        return temp_result;
    }
    
    public /*@ pure @*/ boolean contains(final Predicate a_predicate) {
        return this.contains(a_predicate.getSymbol(), a_predicate.getArity());
    }
}