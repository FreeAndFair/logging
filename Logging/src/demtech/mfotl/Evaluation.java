package demtech.mfotl;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class Evaluation {
    // Attributes
    private final List<String> my_variables;
    private final Set<VarAssigns> my_var_assign;
    private final Set<VarAssigns> my_neg_assign;
    private int my_state; // 0 false, 1 true, -1 satisfiable
    private static final Logger my_logger = new Logger();

    // Constructors
    public Evaluation() {
        my_var_assign = new HashSet();
        my_neg_assign = new HashSet();
        my_variables = new LinkedList();
        my_state = 0;
    }
    
    public Evaluation(final Collection<String> the_free_var) {
        my_var_assign = new HashSet();
        my_neg_assign = new HashSet();
        if (the_free_var == null) {
            my_variables = new LinkedList();
        } else {
            my_variables = new LinkedList(the_free_var);
        }
        my_state = -1;
    }
    
    public Evaluation(final Evaluation a_valuation) {
        this.my_var_assign = new HashSet(a_valuation.my_var_assign);
        this.my_neg_assign = new HashSet(a_valuation.my_neg_assign);
        this.my_variables = new LinkedList(a_valuation.my_variables);
        this.my_state = a_valuation.my_state;
    }
    
    // Public Methods
    
    // For Atomic Formulas
    public void addVarAssign(final Set<VarAssigns> a_assign_set) {
        this.my_var_assign.addAll(a_assign_set);
    }
    
    // For conjunction, TODO rewrite
    public void conjunction(final Evaluation a_valuation) { // A & B
        if (this.my_state == 0 || a_valuation.my_state == 0) {
            for (String s_i : a_valuation.my_variables) {
                if (!this.my_variables.contains(s_i)) {
                    this.my_variables.add(s_i);
                }
            }
            this.my_state = 0; // unsatisfiable
            
            this.my_var_assign.clear();
            this.my_neg_assign.clear();
            return;
        }
        
        if (this.my_state == 1 && a_valuation.my_state == 1) {
            for (String s_i : a_valuation.my_variables) {
                if (!this.my_variables.contains(s_i)) {
                    this.my_variables.add(s_i);
                }
            }
            this.my_state = 1; // valid
            
            this.my_var_assign.clear();
            this.my_neg_assign.clear();
            return;
        }
        
        if (a_valuation.my_state == 1) {
            for (String s_i : a_valuation.my_variables) {
                if (!this.my_variables.contains(s_i)) {
                    this.my_variables.add(s_i);
                }
            }
            return;
        }
        
        if (this.my_state == 1) {
            for (String s_i : a_valuation.my_variables) {
                if (!this.my_variables.contains(s_i)) {
                    this.my_variables.add(s_i);
                }
            }
            this.my_state = a_valuation.my_state;
            this.my_neg_assign.clear();
            this.my_neg_assign.addAll(a_valuation.my_neg_assign);
            this.my_var_assign.clear();
            this.my_var_assign.addAll(a_valuation.my_var_assign);
            return;
        }
        
        // TODO fix following cases
        //if this.my_sate == -1 && a_valuation.my_satebb == -1
        
        for (String s_i : a_valuation.my_variables) {
            if (!this.my_variables.contains(s_i)) {
                this.my_variables.add(s_i);
            }
        }
        retainAll(this.my_var_assign, a_valuation.my_var_assign);
        this.my_neg_assign.addAll(a_valuation.my_neg_assign);
        this.my_state = -1;
        if (this.my_var_assign.isEmpty() && this.my_neg_assign.isEmpty()) {
            this.my_state = 0;
        }
    }
    
    // For negation
    public void negation() {
        if (this.my_state == 1) {
            this.my_state = 0;
        } else if (this.my_state == 0) {
            this.my_state = 1;
        } else { // if my_state == -1
            final Set temp = new HashSet(this.my_neg_assign);
            this.my_neg_assign.clear();
            this.my_neg_assign.addAll(my_var_assign);
            this.my_var_assign.clear();
            this.my_var_assign.addAll(temp);
        }
    }
    
    // For existential check
    public void removeBoundVar(final Set<String> the_bound_var) {
        my_logger.debug("InMethod: Evaluation.removeBoundVar");
        my_logger.debug(the_bound_var);

        // positioning
        for (String str_i : the_bound_var) {
            my_logger.debug("Remove free var: " + str_i);
            if (my_variables.remove(str_i)) {
                for (VarAssigns va_i : this.my_var_assign) {
                    va_i.remove(str_i);
                }
                for (VarAssigns va_i : this.my_neg_assign) {
                    va_i.remove(str_i);
                }
            }
        }
    }
    
    //@ pure
    public boolean isTrue() {
        return (this.my_state == 1 || this.my_state == -1);
    }
    
    //@ pure
    public int getSize() {
        return this.my_variables.size();
    }
    
    //@ pure
    public Set<int[]> getSet() {
        Set<int[]> result_set = new HashSet();
        for (VarAssigns va_i : this.my_var_assign) {
            int[] int_array = va_i.getArray();
            result_set.add(int_array);
        }
        return result_set;
    }
    
    //@ pure
    public String toString() {
        String result_temp_string = this.my_variables.toString() + "\nASSIGN: ";
        
        for (VarAssigns i : this.my_var_assign) {
            result_temp_string = result_temp_string.concat(i.toString() + " \n");
        }
        
        result_temp_string = result_temp_string.concat("NEG: ");
        
        for (VarAssigns i : this.my_var_assign) {
            result_temp_string = result_temp_string.concat(i.toString() + " \n");
        }
        
        return result_temp_string;
    }
    
    // Protected Methods
    
    //@ pure
    protected int getState() {
        return this.my_state;
    }
    
    //@ assignable my_state;
    protected void setState(final int a_state) {
        if (a_state >= -1 && a_state <= 1) {
            this.my_state = a_state;
        }
    }
    
    // Private Methods
    /*
    private void removeAll(final Set<List> a_src, final Set<List> a_dst) {
        if (a_src.isEmpty() || a_dst.isEmpty()) {
            return;
        }
        
        for (List<VarAssigns> list_i : a_src) {
            boolean remove_list = false; 
            for (List<VarAssigns> list_j : a_dst) {
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
        
        for (List<VarAssigns> list_i : a_src) {
            for (List<VarAssigns> list_j : a_dst) {
                if (compatible(list_i, list_j)) {
                    for (VarAssigns va_i : list_j) {
                        if (!listContains(list_i, va_i)) {
                            list_i.add(va_i);
                        }
                    }
                }
            }
        }
    }
    
    //@ pure
    private boolean compatible(final List<VarAssigns> a_src, final List<VarAssigns> a_dst) {
        for (VarAssigns va_i : a_src) {
            for (VarAssigns va_j : a_dst) {
                if (va_i.getName().equals(va_j.getName()) && (va_i.getValue() != va_j.getValue())) {
                        return false;
                }
            }
        }
        return true;
    }
    
    //@ pure
    private boolean listContains(final List<VarAssigns> a_list, final VarAssigns a_va) {
        for (VarAssigns va_i : a_list) {
            if (va_i.vequals(a_va)) {
                return true;
            }
        }
        return false;
    }*/
    

    // Get the intersection of two sets, TODO implement
    private void retainAll(final Set<VarAssigns> a_src, final Set<VarAssigns> a_dst) {
        for (VarAssigns va_i : a_src) {
            for (VarAssigns va_j : a_dst) {
                my_logger.debug(va_i.toString() + " <+> " + va_j.toString());
                if (!va_i.retain(va_j)) {
                    my_logger.debug("Don't concat conflict");
                    a_src.remove(va_i);
                    my_logger.debug("Left Size" + a_src.size());
                }
            }
        }
    }
}

class VarAssigns {
    // Attributes
    private final List<String> my_names;
    private final List<Integer> my_values;
    
    // Constructor
    public VarAssigns() {
        my_names = new LinkedList();
        my_values = new LinkedList();
    }
    
    // Public Methods
    
    public List getNames() {
        return this.my_names;
    }
    
    public List getValues() {
        return this.my_values;
    }
    
    public boolean retain(final VarAssigns a_dst) {
        for (int i = 0; i < a_dst.my_names.size(); i++) {
            if (this.my_names.contains(a_dst.my_names.get(i))) {
                if (a_dst.my_values.get(i) != this.my_values.get(this.my_names.indexOf(a_dst.my_names.get(i)))) {
                    this.my_names.clear();
                    this.my_values.clear();
                    return false;
                }
            } else {
                this.add(a_dst.my_names.get(i), a_dst.my_values.get(i));
            }
        }
        return true;
    }
    
    public void add(final String a_var, final int a_val) {
        my_names.add(a_var);
        my_values.add(a_val);
    }
    
    public boolean remove(final String a_var_name) {
        final int temp_i = my_names.indexOf(a_var_name);
        
        if (temp_i != -1) {
            my_names.remove(temp_i);
            my_values.remove(temp_i);
        }
        
        return (temp_i != -1);
    }
    
    //@ pure
    public int[] getArray() {
        int[] result_array = new int[this.my_values.size()];
        for (int i = 0; i < result_array.length; i++) {
            result_array[i] = this.my_values.get(i);
        }
        return result_array;
    }
    
    //@ pure
    public String toString() {
        String result_str = "(";
        for (int i = 0; i < my_names.size(); i++) {
            result_str += ((String)my_names.get(i) + ":" + (Integer)my_values.get(i) + " ");
        }
        result_str += ")";
        
        return result_str;
    }
}