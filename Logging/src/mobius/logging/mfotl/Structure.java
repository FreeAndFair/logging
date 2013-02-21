package mobius.logging.mfotl;

//TODO add specs and docs

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Structure {
    private final Map my_variable_assignment;
    private final Map my_relation_assignment;
    //private final static Map constant_valuation = new Hashtable();
    
    /*
     * initialization of Structure
     */
    public Structure() {
        my_variable_assignment = new Hashtable();
        my_relation_assignment = new Hashtable();
    }
    
    /*
     * evaluate variables
     */
    public int evaluateVar(final /*@ non_null @*/ String _name) {
        int temp_int;
        try {
            temp_int = Integer.parseInt(_name);
        }
        catch(NumberFormatException nfe) {
            temp_int = (Integer) my_variable_assignment.get(_name);            
        }
        
        return temp_int;
    }
    
    /*
     * add variable assignment
     */
    public void addVarAssign(final String _name, final int _value) {
        my_variable_assignment.put(_name, _value);
    }
    
    public void initRelationAssign(final String _name) {
        my_relation_assignment.put(_name, new RelationAssignment());
    }
    
    /*
     * add relation assignment
     */
    public void addAssign(final String _name, final int[] _value) {
        final RelationAssignment temp_rel_assign = (RelationAssignment)my_relation_assignment.get(_name);
        temp_rel_assign.addRelation(_value);
    }
    
    public boolean evaluateRelation(final /*@ non_null @*/ String _name, final /*@ non_null @*/ int[] _value) {
        if ("=".equals(_name)) {
            return ((_value.length == 2) && (_value[0] == _value[1]));
        } else if ("<".equals(_name)) {
            return ((_value.length == 2) && (_value[0] < _value[1]));
        } else {
            final RelationAssignment temp_rel_assign = (RelationAssignment)my_relation_assignment.get(_name);
            return temp_rel_assign.belongtoRelation(_value);
        }
    }
}

class RelationAssignment {
    private final Set my_assignment;

    public RelationAssignment() {
        my_assignment = new HashSet();
    }
    
    public void addRelation(final int[] _val) {
        final List tmp_list = new ArrayList();
        for (int i = 0; i < _val.length; i++) {
            tmp_list.add(_val[i]);
        }
        my_assignment.add(tmp_list);
    }
    
    
    /*
     * check if a set of values belongs to a relationship
     */
    public boolean belongtoRelation(final int[] _value) {
        final Set tmp_set = new HashSet();
        for (int i = 0; i < _value.length; i++) {
            tmp_set.add(_value[i]);
        }
        
        return my_assignment.contains(tmp_set);
    }
}