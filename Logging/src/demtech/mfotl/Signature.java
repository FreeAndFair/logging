package demtech.mfotl;

import java.util.Set;
import java.util.HashSet;


public class Signature {
    // Attributes
    final private Set<Predicate> my_predicate;
    
    // Constructor
    public Signature() {
        my_predicate = new HashSet();
        
        this.addPredicate(new Predicate("True", 0));
        this.addPredicate(new Predicate("False", 0));
    }
    
    // Public Methods
    public final void addPredicate(final Predicate a_predicate) {
        my_predicate.add(a_predicate);
    }
    
    //@ pure
    public final boolean contains(final String a_name, final int a_arity) {
        boolean temp_result = false;
        for (Predicate i : my_predicate) {
            if (a_name.equals(i.getName()) && (i.getArity() == a_arity)) {
                temp_result = true;
                break;
            }
        }
        return temp_result;
    }
    
    //@ pure
    public final boolean contains(final Predicate a_predicate) {
        return this.contains(a_predicate.getName(), a_predicate.getArity());
    }
}