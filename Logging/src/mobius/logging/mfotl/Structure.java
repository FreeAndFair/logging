package mobius.logging.mfotl;

import java.util.Hashtable;
import java.util.Set;

public class Structure {
    public Hashtable assignment;
    
    public Structure() {
        assignment = new Hashtable();
    }
    
    public int evaluation(final /*@ non_null @*/ String _name) {
        return (Integer) assignment.get(_name);
    }
    
    public void addAssign(final String _name, final int _value) {
        assignment.put(_name, _value);
    }   
}

/*
class Constant {
    int[] element;
}*/