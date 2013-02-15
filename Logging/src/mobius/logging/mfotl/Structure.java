package mobius.logging.mfotl;

//TODO add specs and docs

import java.util.HashSet;
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

class RelationAssignment {
    private final String name;
    private final int arity;
    private final Set assignment;
    
    public RelationAssignment(final String _name, final int _arity) {
        name = _name;
        arity = _arity;
        assignment = new HashSet();
    }
    
    /*@ ensures _val.length == arity @*/
    public void addRelation(final int[] _val) {
        final Set tmp_set = new HashSet();
        for (int i = 0; i < _val.length; i++) {
            tmp_set.add(_val[i]);
        }
        assignment.add(tmp_set);
    }
    
    public boolean belongtoRelation(final int[] _val) {
        final Set tmp_set = new HashSet();
        for (int i = 0; i < _val.length; i++) {
            tmp_set.add(_val[i]);
        }
        
        return assignment.contains(tmp_set);
    }
    
    public String getName() {
        return name;
    }
    
    public int getArity() {
        return arity;
    }
}