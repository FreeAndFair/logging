package mobius.logging.mfotl;

import java.util.Hashtable;
import java.util.Set;

public class Structure {
    private Hashtable assignment;
       
    public Structure() {
        assignment = new Hashtable();
    }
    
    public int evaluation(final /*@ non_null @*/ String _name) {
        return (Integer) assignment.get(_name);
    }
    
    public void addAssign(final String _name, final int _value) {
        assignment.put(_name, _value);
    }
    
    public boolean evaluation(final /*@ non_null @*/ String _name, final /*@ non_null @*/ int[] _val) {
        return false;
    }
}

/*
class Constant {
    int[] element;
}*/

class RelationAssignment {
    private String name;
    private int arity;
    private Set assignment;
    
    public RelationAssignment(final String _name, final int _arity) {
        name = _name;
        arity = _arity;
        
        //assignment = new Set();
        //assignment = new Set[arity];
    }
    
    
    public void addRelationship(final int[] _val) {
        // review Jian how to use SET??
        //Set tmp = new Set();
        Set tmp = null;
        for (int i = 0; i < _val.length; i++) {
            tmp.add(_val[i]);
        }
        
        assignment.add(tmp);
    }
    
    
}