package mobius.logging.mfotl;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class Evaluation {
    // Attributes
    private final Set<List> my_variable_assign;
    private boolean my_var_all = false;
    private final Set<List> my_neg_variable_assign;
    private boolean my_neg_all = true;
    private final List<String> my_variables;
    private static final Logger my_logger = new Logger();

    // Constructors
    public Evaluation() {
        my_variable_assign = new HashSet();
        my_neg_variable_assign = new HashSet();
        my_variables = new LinkedList();
    }
    
    public Evaluation(final List<String> the_free_var) {
        my_variable_assign = new HashSet();
        my_neg_variable_assign = new HashSet();
        my_variables = new LinkedList(the_free_var);
    }
    
    public Evaluation(final Evaluation a_valuation) {
        this.my_variable_assign = new HashSet(a_valuation.my_variable_assign);
        this.my_neg_variable_assign = new HashSet(a_valuation.my_neg_variable_assign);
        this.my_variables = new LinkedList(a_valuation.my_variables);
    }
    
    // Public Methods
    public void addVarAssign(final Set<List> a_assign_set) {
        this.my_variable_assign.addAll(a_assign_set);
    }
    
    // For conjunction
    public void conjunction(final Evaluation a_valuation) { // A & B
        if (!this.isTrue() || !a_valuation.isTrue()) { // Right hand side B is unsatisfiable
            this.my_variable_assign.clear();
            this.my_var_all = false;
            this.my_neg_variable_assign.clear();
            this.my_neg_all = true;
            return;
        }
        
        if (this.my_var_all) { // A is valid, copy everything from B
            this.my_variable_assign.clear();
            this.my_variable_assign.addAll(a_valuation.my_variable_assign);
            this.my_var_all = a_valuation.my_var_all;
            this.my_neg_variable_assign.clear();
            this.my_neg_all = false;
        } else {
            if (a_valuation.my_var_all) { // B is valid, A stays unchanged
                return;
            } else { // Neither A nor B is valid
                retainAll(this.my_variable_assign, a_valuation.my_variable_assign); // intersection of A, B variable assign
                addAll(this.my_neg_variable_assign, a_valuation.my_neg_variable_assign); // union of A, B negation variable assign
            }
        }
    }
    
    private void retainAll(final Set<List> a_src, final Set<List> a_dst) {
        
    }
    
    // For negation
    public void negation() {
        final Set temp = new HashSet(this.my_neg_variable_assign);
        final boolean temp_b = this.my_neg_all;
        this.my_neg_variable_assign.clear();
        this.my_neg_variable_assign.addAll(my_variable_assign);
        this.my_neg_all = this.my_var_all;
        this.my_variable_assign.clear();
        this.my_variable_assign.addAll(temp);
        this.my_var_all = temp_b;
    }
    
    // For existential check
    public void removeBoundVar(final Set the_bound_var) {
        my_logger.debug("InMethod: Evaluation.removeBoundVar");
        my_logger.debug(the_bound_var);
        for (List<VariableAssign> j : this.my_variable_assign) {
            final Set<VariableAssign> temp_set = new HashSet();
            for (VariableAssign k : j) {
                if (the_bound_var.contains(k.getName())) {
                    temp_set.add(k);
                    my_logger.debug("Remove free var: " + k.toString());
                } else {
                    my_logger.debug(k.getName() + " is not bound");
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
                temp_array[j] = i.get(j).getValue();
            }
            result_set.add(temp_array);
        }
        return result_set;
    }
    
    public Set<int[]> getNegSet() {
        final Set<int[]> result_set = new HashSet();
        for (List<VariableAssign> i : this.my_neg_variable_assign) {
            final int[] temp_array = new int[i.size()];
            for (int j = 0; j < i.size(); j++) {
                temp_array[j] = i.get(j).getValue();
            }
            result_set.add(temp_array);
        }
        return result_set;
    }
    
    //@ pure
    public boolean isTrue() {
        boolean result_b;
        
        if (this.my_neg_all) {
            if (this.my_var_all) {
                result_b = true;
            } else {
                result_b = this.my_variable_assign.isEmpty() ^ true;
            }
        } else {
            if (this.my_var_all) {
                result_b = true;
            } else {
                result_b = (!this.my_neg_variable_assign.isEmpty()) || (!this.my_variable_assign.isEmpty());
            }
        }
        
        return result_b;
    }
    
    //@ assignable my_neg_all;
    public void setNegAll(final boolean a_value) {
        this.my_neg_all = a_value;
    }
    
    //@ pure
    public boolean isNegAll() {
        return this.my_neg_all;
    }
    
    //@ assignable my_var_all;
    public void setVarAll(final boolean a_value) {
        this.my_var_all = a_value;
    }
    
    //@ pure
    public boolean isVarAll() {
        return this.my_var_all;
    }
    
    //@ pure
    public int getSize() {
        return this.my_variables.size();
    }
    
    //@ pure
    public String toString() {
        String result_temp_string = this.my_variables.toString() + "\nASSIGN: ";
        
        for (List<int[]> i : this.my_variable_assign) {
            for (int j = 0; j < i.size(); j++) {
                result_temp_string = result_temp_string.concat(i.toString() + " ");
            }
            result_temp_string = result_temp_string.concat("\n");
        }
        
        result_temp_string = result_temp_string.concat("\nNEG: ");
        
        for (List<int[]> i : this.my_variable_assign) {
            for (int j = 0; j < i.size(); j++) {
                result_temp_string = result_temp_string.concat(i.toString() + " ");
            }
            result_temp_string = result_temp_string.concat("\n");
        }
        
        return result_temp_string;
    }
    
    // Private Methods
    private void removeAll(final Set<List> a_src, final Set<List> a_dst) {
        if (a_src.isEmpty() || a_dst.isEmpty()) {
            return;
        }
        
        for (List<VariableAssign> list_i : a_src) {
            boolean remove_list = false; 
            for (List<VariableAssign> list_j : a_dst) {
                if (compatible(list_i, list_j)) {
                    remove_list = true;
                }
            }

            if (remove_list) {
                a_src.remove(list_i);
            }
        }
    }
    
    private void addAll(final Set<List> a_src, final Set<List> a_dst) {
        if (a_dst.isEmpty()) {
            return;
        }
        
        for (List<VariableAssign> list_i : a_src) {
            for (List<VariableAssign> list_j : a_dst) {
                if (compatible(list_i, list_j)) {
                    for (VariableAssign va_i : list_j) {
                        if (!listContains(list_i, va_i)) {
                            list_i.add(va_i);
                        }
                    }
                }
            }
        }
    }
    
    //@ pure
    private boolean compatible(final List<VariableAssign> a_src, final List<VariableAssign> a_dst) {
        for (VariableAssign va_i : a_src) {
            for (VariableAssign va_j : a_dst) {
                if (va_i.getName().equals(va_j.getName()) && (va_i.getValue() != va_j.getValue())) {
                        return false;
                }
            }
        }
        return true;
    }
    
    //@ pure
    private boolean listContains(final List<VariableAssign> a_list, final VariableAssign a_va) {
        for (VariableAssign va_i : a_list) {
            if (va_i.vequals(a_va)) {
                return true;
            }
        }
        return false;
    }
}


class VariableAssign {
    private final String my_name;
    private final int my_value;
    
    public VariableAssign(final String a_name, final int a_value) {
        my_name = a_name;
        my_value = a_value;
    }
    
    public String getName() {
        return this.my_name;
    }
    
    public int getValue() {
        return this.my_value;
    }
    
    public boolean vequals(final VariableAssign a_va) {
        return (this.my_name.equals(a_va.getName()) && (this.my_value == a_va.getValue()));
    }
    
    public String toString() {
        return "(" + my_name + ": " + my_value + ")";
    }
}