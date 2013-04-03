package mobius.logging.mfotl;

//TODO add specs and docs

import java.util.Arrays;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
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
        
        return result_temp_string;
    }
}

class VariableAssign {
    public final String my_name;
    public final int my_value;
    
    public VariableAssign(final String a_name, final int a_value) {
        my_name = a_name;
        my_value = a_value;
    }
    
    public String toString() {
        return "(" + my_name + ": " + my_value + ")";
    }
}

class Valuation {
    // Attributes
    private final Set<List> my_variable_assign;
    private boolean my_var_all = false;
    private final Set<List> my_neg_variable_assign;
    private boolean my_neg_all = false;
    private boolean my_truth = false; 
    private static final Logger my_logger = new Logger();

    // Constructor
    public Valuation() {
        my_variable_assign = new HashSet();
        my_neg_variable_assign = new HashSet();
    }
    
    public Valuation(final /*@ non_null @*/ Valuation a_valuation) {
        this.my_variable_assign = new HashSet(a_valuation.my_variable_assign);
        this.my_neg_variable_assign = new HashSet(a_valuation.my_neg_variable_assign);
    }

    public void addVarAssign(final Set a_assign_set) {
        this.my_variable_assign.addAll(a_assign_set);
    }

    public void removeAll(final Valuation a_valuation) {
        for (Object i : a_valuation.my_variable_assign) {
            this.my_variable_assign.remove(i);
        }
    }
    
    public void retainAll(final Valuation a_valuation) { // A & B
        if (!a_valuation.getTruth()) { // Right hand side B is unsatisfiable
            this.my_variable_assign.clear();
            this.my_neg_variable_assign.clear();
            this.my_truth = false;
            return;
        }
        
        if (!a_valuation.my_neg_variable_assign.isEmpty()) { // A & ~B
            this.my_variable_assign.removeAll(a_valuation.my_neg_variable_assign);
            this.my_neg_variable_assign.addAll(a_valuation.my_variable_assign);
        }
        
        this.my_truth = this.my_truth && a_valuation.getTruth();
        
        if (!a_valuation.getSet().isEmpty() && !this.getSet().isEmpty()) {
            this.my_variable_assign.retainAll(a_valuation.my_variable_assign);
            if (this.getSet().isEmpty()) {
                this.my_truth = false;
            }
        }
        if (a_valuation.getSet().isEmpty() && !a_valuation.getTruth()) {
            this.my_variable_assign.clear();
        }
    }
    
    // For negation
    public void negateAll() {
        this.my_truth = !this.my_truth;
        
        final Set temp = new HashSet(this.my_neg_variable_assign);
        this.my_neg_variable_assign.clear();
        this.my_neg_variable_assign.addAll(my_variable_assign);
        this.my_variable_assign.clear();
        this.my_variable_assign.addAll(temp);
    }
    
    // For existential check
    public void removeBoundVar(final Set the_bound_var) {
        for (List<VariableAssign> j : this.my_variable_assign) {
            final Set<VariableAssign> temp_set = new HashSet();
            for (VariableAssign k : j) {
                if (the_bound_var.contains(k.my_name)) {
                    temp_set.add(k);
                    my_logger.debug("Remove free var: " + k.toString());
                }
            }
            j.removeAll(temp_set);
        }
    }
    
    //@ pure
    public boolean isEmpty() {
        if (this.my_variable_assign.isEmpty()) {
            return this.my_neg_variable_assign.isEmpty();
        } else {
            return true;
        }
    }
    
    public Set<int[]> getSet() {
        final Set<int[]> result_set = new HashSet();
        for (List<VariableAssign> i : this.my_variable_assign) {
            final int[] temp_array = new int[i.size()];
            for (int j = 0; j < i.size(); j++) {
                temp_array[j] = i.get(j).my_value;
            }
            result_set.add(temp_array);
        }
        return result_set;
    }
    
    //@ assignable my_truth;
    public void setTruth(final boolean a_value) {
        this.my_truth = a_value;
    }
    
    public boolean getTruth() {
        return this.my_truth;
    }
    
    public String toString() {
        String result_temp_string = "ASSIGN: ";
        
        for (List<VariableAssign> i : this.my_variable_assign) {
            for (int j = 0; j < i.size(); j++) {
                result_temp_string = result_temp_string.concat(i.toString() + " ");
            }
            result_temp_string = result_temp_string.concat("\n");
        }
        
        result_temp_string = result_temp_string.concat("\nNEG: ");
        
        for (List<VariableAssign> i : this.my_variable_assign) {
            for (int j = 0; j < i.size(); j++) {
                result_temp_string = result_temp_string.concat(i.toString() + " ");
            }
            result_temp_string = result_temp_string.concat("\n");
        }
        
        return result_temp_string;
    }
}