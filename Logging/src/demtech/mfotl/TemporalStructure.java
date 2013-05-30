package demtech.mfotl;

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
    public /*@ pure @*/ void insertStructure(final Structure a_structure, final int a_time_stamp) {
        my_structure.add(a_structure);
        my_time_stamp.add(a_time_stamp);
    }
    
    public /*@ pure @*/ Structure getStructure(final int a_pos) {
        return my_structure.get(a_pos);
    }

    /*@ pure @*/
    public void dropStructure(final int a_pos) {
        if (a_pos < my_structure.size()) {
            my_structure.set(a_pos, null);
        }
    }
    
    public /*@ pure @*/ int getTime(final int a_pos) {
        return (int)my_time_stamp.get(a_pos);
    }
    
    public /*@ pure @*/ int getSize() {
        return my_structure.size();
    }
    
    public /*@ pure @*/ String toString() {
        String result_string = "";
        for (int i = 0; i < my_structure.size(); i++) {
            result_string = result_string.concat("{" + my_structure.get(i).toString() 
                    + ", t:" + my_time_stamp.get(i).toString() + "}\n");
        }
        return result_string;
    }
}
