package demtech.mfotl;

import java.util.HashMap;
//import java.util.Set;
import java.util.HashSet;

public class Signature {
    // Attributes
    final private HashSet<Predicate> my_predicate = new HashSet();
    final private HashMap<String, HashSet> my_domain = new HashMap();
    final private HashSet<Integer> my_universe;
    
    // Constructor
    public Signature(HashSet a_universe) {
        this.addPredicate(new Predicate("True", 0), null);
        this.addPredicate(new Predicate("False", 0), null);
        this.my_universe = a_universe;
    }
    
    // Public Methods
    public final void addPredicate(final Predicate a_predicate, final HashSet a_domain) {
        if (this.contains(a_predicate.getName(), -1))
            return;
        my_predicate.add(a_predicate);
        my_domain.put(a_predicate.getName(), null);
    }
    
    //@ pure
    public final boolean contains(final String a_name, final int a_arity) {
        boolean temp_result = false;
        for (Predicate i : my_predicate) {
            if (-1 == a_arity) {
                if (a_name.equals(i.getName())) {
                    temp_result = true;
                    break;
                }
            } else if (a_name.equals(i.getName()) && (i.getArity() == a_arity)) {
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
    
    //@ pure
    public final boolean inUniverse(final int a_int) {
        boolean temp_result = false;
        for (Integer i : my_universe) {
            if (a_int == i.intValue()) {
                temp_result = true;
                break;
            }
        }
        return temp_result;
    }
}