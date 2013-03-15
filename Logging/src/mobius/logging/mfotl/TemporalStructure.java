package mobius.logging.mfotl;

import java.util.ArrayList;
import java.util.List;

/**
 * <cod>TemporalStructure</code>
 */
public class TemporalStructure {
    // Attributes
    public List<Structure> my_structure;
    public List<Integer> my_time_stamp;
    
    // Constructor
    public TemporalStructure() {
        my_structure = new ArrayList();
        my_time_stamp = new ArrayList();
    }
    
    // Public Methods
    public void insertStructure(final Structure a_structure, final int a_time_stamp) {
        my_structure.add(a_structure);
        my_time_stamp.add(a_time_stamp);
    }
    
    //@ pure
    public int getSize() {
        return my_structure.size();
    }
}
