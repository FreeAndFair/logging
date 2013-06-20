package demtech.mfotl;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class Evaluation {
    // Attributes
    private final List<String> my_variables;
    private final Set<VarAssigns> my_var_assign;
    private final Set<VarAssigns> my_neg_assign;
    private int my_is_universal; //
    private int my_state; // 0 false, 1 true, -1 satisfiable
    private static final Logger my_logger = new Logger(true);

    // Constructors
    public Evaluation(final List<String> the_free_var) {
        my_var_assign = new HashSet();
        my_neg_assign = new HashSet();
        if (the_free_var == null) {
            my_variables = new LinkedList();
        } else {
            my_variables = new LinkedList(the_free_var);
        }
        my_state = -1;
        my_is_universal = 0;
    }
    
    public Evaluation(final Evaluation a_valuation) {
        this.my_var_assign = new HashSet(a_valuation.my_var_assign);
        this.my_neg_assign = new HashSet(a_valuation.my_neg_assign);
        this.my_variables = new LinkedList(a_valuation.my_variables);
        this.my_state = a_valuation.my_state;
        this.my_is_universal = a_valuation.my_is_universal;
    }
    
    // Public Methods
    
    // For Atomic Formulas' assignment
    public void addVarAssign(final Set<VarAssigns> a_assign_set) {
        this.my_var_assign.addAll(a_assign_set);
    }
    
    // For conjunction
    public void conjunction(final Evaluation a_valuation) {
        my_logger.warning("&-Eval:\n" + this.toString() + "\n" + a_valuation.toString());
        if (this.my_state == 0 || a_valuation.my_state == 0) {
            my_logger.warning("&-0");
            this.addVariables(a_valuation.my_variables);
            this.my_neg_assign.addAll(a_valuation.my_neg_assign);
            this.setComplete(0);
        } else if (this.my_state == 1 || a_valuation.my_state == 1) {
            my_logger.warning("&-1");
            if (this.my_state*a_valuation.my_state != 1) {
                this.setComplete(0);
                this.my_var_assign.addAll(a_valuation.my_var_assign);
            }
            
            this.addVariables(a_valuation.my_variables);
            this.my_neg_assign.addAll(a_valuation.my_neg_assign);
            
            this.setState();
        } else if (this.my_state == -1 && a_valuation.my_state == -1) {
            my_logger.warning("&--");
            this.addVariables(a_valuation.my_variables);
            this.retainAll(a_valuation);
            
            this.setState();
        }
        my_logger.warning("\n-->\n" + this.toString());
    }
    
    // For negation
    public void negation() {
        my_logger.warning("!-Eval:\n" + this.toString());
        
        final Set temp = new HashSet(this.my_neg_assign);
        this.my_neg_assign.clear();
        this.my_neg_assign.addAll(my_var_assign);
        this.my_var_assign.clear();
        this.my_var_assign.addAll(temp);
        
        this.setComplete(1 - this.my_is_universal);
        my_logger.warning("\n-->\n" + this.toString());
    }
    
    // For existential
    public void removeBoundVar(final Set<String> the_bound_var) {
        my_logger.debug("In Method: Evaluation.removeBoundVar");
        my_logger.debug(the_bound_var);
        my_logger.warning("E-Eval:\n" + this.toString());
        
        for (String str_i : the_bound_var) {
            my_logger.debug("Remove free var: " + str_i);
            if (my_variables.remove(str_i)) {
                if (my_variables.isEmpty() && !this.my_var_assign.isEmpty()) {
                    this.setComplete(1);
                }
                
                final Set<VarAssigns> rem = new HashSet();
                for (VarAssigns va_i : this.my_var_assign) {
                    va_i.remove(str_i);
                    if (va_i.getSize() == 0) {
                        rem.add(va_i);
                    }
                }
                this.my_var_assign.removeAll(rem);

                rem.clear();
                for (VarAssigns va_i : this.my_neg_assign) {
                    va_i.remove(str_i);
                    if (va_i.getSize() == 0) {
                        rem.add(va_i);
                    }
                }
                this.my_neg_assign.removeAll(rem);
            }
        }
        
        this.setState();
        my_logger.warning("\n-->\n" + this.toString());
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
        String result_temp_string = "VAR: " + this.my_variables.toString() + "\nASSIGN: ";
        
        for (VarAssigns i : this.my_var_assign) {
            result_temp_string = result_temp_string.concat(i.toString() + " \n");
        }
        
        result_temp_string = result_temp_string.concat("COMPLETE: " + this.my_is_universal + "\n");
        result_temp_string = result_temp_string.concat("STATE: " + this.my_state + "\n");
        
        result_temp_string = result_temp_string.concat("NEG: ");
        
        for (VarAssigns i : this.my_neg_assign) {
            result_temp_string = result_temp_string.concat(i.toString() + " \n");
        }
        
        return result_temp_string;
    }
    
    // Protected Methods
    //@ pure
    protected int getComplete() {
        return this.my_is_universal;
    }
    
    //@ pure
    protected int getState() {
        return this.my_state;
    }
    
    //@ requires a_is_universal == 0 || a_is_universal == 1;
    //@ assignable my_is_universal
    protected void setComplete(final int a_is_universal) {
        if (a_is_universal == 0 || a_is_universal == 1) {
            this.my_is_universal = a_is_universal;
        }
        
        if (a_is_universal == 0 || a_is_universal == 1) {
            this.my_var_assign.clear();
        }
        
        this.setState();
    }
    
    // Private Methods
    //@ assignable my_state
    private void setState() {
        my_logger.warning("SIZE: " + this.my_var_assign.size() + " + " + this.my_neg_assign.size());
        if (this.my_is_universal == 0) {
            if (this.my_var_assign.isEmpty()) {
                this.my_state = 0;
            } else {
                this.my_state = -1;
            }
        } else {
            if (this.my_neg_assign.isEmpty()) {
                this.my_state = 1;
            } else {
                this.my_state = -1;
            }
        }
    }
    
    // Get the cross production intersection of two sets
    private void retainAll(final Evaluation a_valuation) {
        final Set rem = new HashSet();
        if (a_valuation.getComplete() == 0) {
            for (VarAssigns va_i: this.my_var_assign) {
                for (VarAssigns va_j: a_valuation.my_var_assign) {
                    final VarAssigns va_tmp = new VarAssigns(va_i);
                    va_tmp.addAll(va_j);
                    if (va_tmp.solveConflict()) {
                        this.my_var_assign.add(va_tmp);
                    }
                }
                rem.add(va_i);
            }
            this.my_var_assign.removeAll(rem);
        }
        
        this.my_neg_assign.addAll(a_valuation.my_neg_assign);

        rem.clear();
        for (VarAssigns va_i: this.my_var_assign) {
            for (VarAssigns va_j: this.my_neg_assign) {
                final VarAssigns va_tmp = new VarAssigns(va_i);
                va_tmp.addAll(va_j);
                if (va_tmp.solveConflict()) {
                    rem.add(va_i);
                    my_logger.warning("SSSSSSSSSSS" + va_i.toString() + "\n" + va_j.toString());
                }
            }
        }
        
        this.my_var_assign.removeAll(rem);
    }
    
    private void addVariables(final List<String> a_variables) {
        for (String s_i : a_variables) {
            if (!this.my_variables.contains(s_i)) {
                this.my_variables.add(s_i);
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
    
    public VarAssigns(final VarAssigns a_va) {
        my_names = new LinkedList(a_va.my_names);
        my_values = new LinkedList(a_va.my_values);
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
    
    public void addAll(final VarAssigns a_va) {
        for (int i = 0; i < a_va.my_names.size(); i++) {
            this.add((String)a_va.getNames().get(i), (Integer)a_va.getValues().get(i));
        }
    }
    
    //@ pure
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
    public boolean solveConflict() {
        final Set<Integer> rem = new HashSet();
        boolean result = true;
        for(int i = 0; i < this.my_names.size(); i++) {
            final int last = this.my_names.lastIndexOf(this.my_names.get(i));
            if (i != last) {
                if (this.my_values.get(i).compareTo(this.my_values.get(last)) == 0) {
                    rem.add(i);
                } else {
                    result = false;
                }
            }
        }
        
        for (Integer i : rem) {
            this.my_names.remove((int)i);
            this.my_values.remove((int)i);
        }
        
        return result;
    }
    
    //@ pure
    public int getSize() {
        return this.my_names.size();
    }
    
    //@ pure
    public String toString() {
        String result_str = "(";
        for (int i = 0; i < my_names.size(); i++) {
            result_str += ((String)my_names.get(i) + ":" + (Integer)my_values.get(i) + " ");
        }
        
        result_str = result_str.concat(")");
        
        return result_str;
    }
}