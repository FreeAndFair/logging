package mobius.logging.mfotl;

import java.util.ArrayList;
import java.util.List;

/**
 * <cod>TemporalStructure</code>
 */
public class TemporalStructure {
    // Attributes
    private final List<Structure> my_structure;
    private final List<Integer> my_time_stamp;
    
    // Constructor
    //@ assignable my_structure;
    //@ assignable my_time_stamp;
    public TemporalStructure() {
        my_structure = new ArrayList();
        my_time_stamp = new ArrayList();
    }
    
    // Public Methods
    //@ pure
    public void insertStructure(final Structure a_structure, final int a_time_stamp) {
        my_structure.add(a_structure);
        my_time_stamp.add(a_time_stamp);
    }
    
    //@ pure
    public Structure getStructure(final int a_pos) {
        return my_structure.get(a_pos);
    }
    
    //@ pure
    public int getTime(final int a_pos) {
        if (a_pos > my_time_stamp.size()) {
            return (int)my_time_stamp.get(my_time_stamp.size());
        } else {
            return (int)my_time_stamp.get(a_pos);
        }
    }
    
    //@ pure
    public int getSize() {
        return my_structure.size();
    }
}
