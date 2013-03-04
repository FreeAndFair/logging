package mobius.logging.mfotl;

//TODO add specs and docs

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Structure implements Cloneable{
    // Attributes
    private final Map my_variable_assignment;
    private final Map my_relation_assignment;
    private final Logger logger = new Logger();
    
    // Constructors
    /**
     * initialization of Structure
     */
    public Structure() {
        my_variable_assignment = new Hashtable();
        my_relation_assignment = new Hashtable();
    }
    
    // Public Methods
    /**
     * evaluate variables
     * @param _name
     * @return
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
    
    /**
     * add variable assignment
     * @param _name
     * @param _value
     */
    public void addVarAssign(final String _name, final int _value) {
        my_variable_assignment.put(_name, _value);
    }
    
    /**
     * 
     * @param a_relation_name
     */
    public void initRelationAssign(final String a_relation_name) {
        my_relation_assignment.put(a_relation_name, new RelationAssignment());
    }
    
    /**
     * add relation assignment_value
     * @param a_name
     * @param a_value
     */
    public void addRelationAssign(final String a_name, final int[] a_value) {
        final RelationAssignment temp_rel_assign = (RelationAssignment)my_relation_assignment.get(a_name);
        if (temp_rel_assign == null) {
            logger.error("No relation found!!");
        }
        temp_rel_assign.addRelation(a_value);
    }
    
    /**
     * 
     * @param a_name
     * @param a_value
     * @return
     */
    public boolean evaluateRelation(final /*@ non_null @*/ String a_name, final /*@ non_null @*/ int[] a_value) {
        if ("=".equals(a_name)) {
            return ((a_value.length == 2) && (a_value[0] == a_value[1]));
        } else if ("<".equals(a_name)) {
            return ((a_value.length == 2) && (a_value[0] < a_value[1]));
        } else {
            final RelationAssignment temp_rel_assign = (RelationAssignment)my_relation_assignment.get(a_name);
            return temp_rel_assign.belongtoRelation(a_value);
        }
    }
    
    public Object clone() throws CloneNotSupportedException {
        return super.clone();
    }
}    

class RelationAssignment {
    // Attribute
    private final Set my_assignment;

    // Constructor
    public RelationAssignment() {
        my_assignment = new HashSet();
    }
    
    // Public Methods
    /**
     * 
     * @param a_val
     */
    public void addRelation(final int[] a_val) {
        final List tmp_list = new ArrayList();
        for (int i = 0; i < a_val.length; i++) {
            tmp_list.add(a_val[i]);
        }
        my_assignment.add(tmp_list);
    }
    
    /**
     * check if a set of values belongs to a relationship
     * @param a_value
     * @return
     */
    public boolean belongtoRelation(final int[] a_value) {
        final Set tmp_set = new HashSet();
        for (int i = 0; i < a_value.length; i++) {
            tmp_set.add(a_value[i]);
        }
        
        return my_assignment.contains(tmp_set);
    }
    
    //@ pure
    public Set getRelationAssign() {
        return my_assignment;
    }
}