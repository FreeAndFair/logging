package mobius.logging.mfotl;

import java.util.Hashtable;;

public class Structure {
    public Hashtable assignment;
    
    public Structure() {
        assignment = new Hashtable();
    }
    
    public boolean evaluation(final /*@ non_null @*/ Formula _formula) {
            
        return _formula.temporal_formula.is_true;
    }
}

class Constant {
    int[] element;
}