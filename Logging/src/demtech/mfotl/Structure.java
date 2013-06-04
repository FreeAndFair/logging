package demtech.mfotl;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Map;
import java.util.Set;

public class Structure {
    // Attributes
    private final Map my_relation_assignment;
    private final Set my_nullary_relation;
    private static final Logger my_logger = new Logger();
    
    // Constructors
    public Structure() {
        my_relation_assignment = new Hashtable();
        my_nullary_relation = new HashSet();
        addNullaryRelation("True");
    }
    
    public Structure(final Structure a_structure) {
        this.my_relation_assignment = new Hashtable(a_structure.my_relation_assignment);
        this.my_nullary_relation = new HashSet(a_structure.my_nullary_relation);
        addNullaryRelation("True");
    }
    
    // Public Methods
    
    public void initRelationAssign(final String a_relation_name) {
        if (!my_relation_assignment.containsKey(a_relation_name)) {
            my_relation_assignment.put(a_relation_name, new HashSet<int[]>());
        }
    }
    
    /**
     * add relation assignment_value
     * @param a_name
     * @param a_value
     */
    public void addRelationAssign(final String a_name, final int[] a_value) {
        final Set<int[]> temp_rel_assign = (HashSet<int[]>) my_relation_assignment.get(a_name);
        if (temp_rel_assign == null) {
            my_logger.error("No relation " + a_name + " found!!");
        }
        final int[] temp_val = new int[a_value.length];
        System.arraycopy(a_value, 0, temp_val, 0, a_value.length);
        if (!setContains(temp_rel_assign, temp_val)) {
            temp_rel_assign.add(temp_val);
        }
    }

    /**
     * 
     * @param a_name
     * @param a_ra
     */
    public void addRelationAssign(final String a_name, final Set<int[]> a_ra) {
        final Set<int[]> temp_rel_assign = (HashSet<int[]>) my_relation_assignment.get(a_name);
        if (temp_rel_assign == null) {
            my_logger.fatal("Rel: " + a_name + " is Empty!");
        }
        if (a_ra == null) {
            return;
        }
        for (int[] i : a_ra) {
            temp_rel_assign.add(i);
        }
    }
    
    public void removeRelationAssign(final String a_name, final int[] a_value) {
        final Set<int[]> temp_rel_assign = (HashSet<int[]>) my_relation_assignment.get(a_name);
        if (temp_rel_assign == null) {
            my_logger.fatal("Rel: " + a_name + " is Empty!");
        }
        if (a_value == null) {
            return;
        }
        for (int[] i : temp_rel_assign) {
            if (Arrays.equals(a_value, i)) {
                temp_rel_assign.remove(i);
            }
        }
    }
    
    public Set<int[]> getRelationAssign(final String a_name) {
        return (Set<int[]>) my_relation_assignment.get(a_name);
    }

    
    public final void addNullaryRelation(final String a_name) {
        this.my_nullary_relation.add(a_name);
    }
    
    public boolean containsNullaryRelation(final String a_name) {
        return this.my_nullary_relation.contains(a_name);
    }

    public String toString() {
        String result_temp_string = "";

        for (Object i : my_relation_assignment.keySet()) {
            result_temp_string = result_temp_string.concat((String)i + ":");

            String temp_result = "{";
            for (int[] j: this.getRelationAssign((String)i)) {
                temp_result = temp_result.concat("[");
                for (int k = 0; k < j.length; k++) {
                    temp_result = temp_result.concat(j[k] + "");
                    if (k != j.length-1) {
                        temp_result = temp_result.concat(" ");
                    }
                }
                temp_result = temp_result.concat("]");
            }
            temp_result = temp_result.concat("}");
            
            result_temp_string = result_temp_string.concat(temp_result);
        }
        
        for (Object obj_i : my_nullary_relation) {
            result_temp_string = result_temp_string.concat(" " + ((String)obj_i));
        }
        
        return result_temp_string;
    }
    
    //@ pure
    private boolean setContains(final Set<int[]> a_set, final int[] a_array) {
        if (a_set == null || a_array == null) {
            return false;
        }
        for (int[] temp_i : a_set) {
            if (Arrays.equals(temp_i, a_array)) {
                return true;
            }
        }
        return false;
    }
}