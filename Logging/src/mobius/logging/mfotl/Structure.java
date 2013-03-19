package mobius.logging.mfotl;

//TODO add specs and docs

import java.util.Arrays;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Map;
import java.util.Set;

public class Structure {
    // Attributes
    private final Map my_relation_assignment;
    private static final Logger my_logger = new Logger();
    
    // Constructors
    public Structure() {
        my_relation_assignment = new Hashtable();
    }
    
    public Structure(final Structure a_structure) {
        this.my_relation_assignment = new Hashtable(a_structure.my_relation_assignment);

    }
    
    // Public Methods
    
    /**
     * 
     * @param a_relation_name
     */
    public void initRelationAssign(final /*@ non_null @*/ String a_relation_name) {
        my_relation_assignment.put(a_relation_name, new HashSet<int[]>());
    }
    
    /**
     * add relation assignment_value
     * @param a_name
     * @param a_value
     */
    public void addRelationAssign(final String a_name, final int[] a_value) {
        final Set<int[]> temp_rel_assign = (HashSet<int[]>) my_relation_assignment.get(a_name);
        if (temp_rel_assign == null) {
            my_logger.error("No relation found!!");
        }
        final int[] temp_val = new int[a_value.length];
        System.arraycopy(a_value, 0, temp_val, 0, a_value.length);
        temp_rel_assign.add(temp_val);
    }
    
    /**
     * 
     * @param a_name
     * @param a_ra
     */
    public void addRelationAssign(final String a_name, final Set<int[]> a_ra) {
        final Set<int[]> temp_rel_assign = (HashSet<int[]>) my_relation_assignment.get(a_name);
        for (int[] i : a_ra) {
            temp_rel_assign.add(i);
        }
    }
    
    public Set<int[]> getRelationAssign(final String a_name) {
        return (Set<int[]>) my_relation_assignment.get(a_name);
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
            final Set<int[]> temp_rel_assign = (Set<int[]>) my_relation_assignment.get(a_name);
            for (int[] i : temp_rel_assign) {
                if (Arrays.equals(i, a_value))
                    return true;
            }
            return false;
        }
    }
    
    public String toString() {
        String result_temp_string = "";

        for (Object i : my_relation_assignment.keySet()) {
            result_temp_string = result_temp_string.concat(" " + (String)i);
            

            String temp_result = "{";
            for (int[] j: this.getRelationAssign((String)i)) {
                temp_result = temp_result.concat("[");
                for (int k = 0; k < j.length; k++) {
                    temp_result = temp_result.concat("" + j[k] + " ");
                }
                temp_result = temp_result.concat("] ");
            }
            temp_result = temp_result.concat("}");
            
            result_temp_string = result_temp_string.concat(temp_result);
            
            result_temp_string = result_temp_string.concat("\n");
        }
        
        return result_temp_string;
    }
}

class Valuation {
    // Attributes
    private final Map my_variable_assignment;
    private static final Logger my_logger = new Logger();

    // Constructor
    public Valuation() {
        my_variable_assignment = new Hashtable();
    }
    
    public Valuation(final /*@ non_null @*/ Valuation a_valuation) {
        this.my_variable_assignment = new Hashtable(a_valuation.my_variable_assignment);
    }

    /**
     * evaluate variables
     * @param a_name
     * @return
     */
    public int evaluateVar(final /*@ non_null @*/ String a_name) {
        int temp_int = 0;
        
        try {
            temp_int = Integer.parseInt(a_name);
            my_logger.debug("Evaluate Constant: " + temp_int);
        }
        catch(NumberFormatException nfe) {
            if (my_variable_assignment.containsKey(a_name)) {
                temp_int = (Integer) my_variable_assignment.get(a_name);
                my_logger.debug("Evaluate Var: " + a_name + " to " + temp_int);
            } else {
                my_logger.fatal("No variable assignment found");
                System.exit(1);
            }
        }
        
        return temp_int;
    }

    /**
     * add variable assignment
     * @param a_name
     * @param a_value
     */
    public void addVarAssign(final /*@ non_null @*/ String a_name, final int a_value) {
        my_variable_assignment.put(a_name, a_value);
    }

    public String toString() {
        String result_temp_string = "";
        
        for (Object i : my_variable_assignment.keySet()) {
            result_temp_string = result_temp_string.concat(" " + (String)i);
            result_temp_string = result_temp_string.concat(":=");
            result_temp_string = result_temp_string.concat(" " + (Integer)my_variable_assignment.get(i) + ", ");
        }
        
        return result_temp_string;
    }
}