package demtech.mfotl;

public class Predicate {
    // Attributes
    private final String my_name;
    private final int my_arity;
    
    // Constructor
    //@ ensures a_arity >= 0;
    public Predicate(final String a_name, final int a_arity) {
        my_name = a_name;
        my_arity = a_arity;
    }
    
    // Public Methods
    //@ pure
    public String toString() {
        return (my_name + "[arity =" + my_arity + "]");
    }
    
    //@ ensures \result == my_name;
    //@ pure
    public String getName() {
        return my_name;
    }
    
    //@ ensures \result == my_arity;
    //@ pure
    public int getArity() {
        return my_arity;
    }
}
