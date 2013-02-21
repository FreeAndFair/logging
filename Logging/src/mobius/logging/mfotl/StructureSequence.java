package mobius.logging.mfotl;

import java.util.ArrayList;
import java.util.List;

/*
 * 
 */
public class StructureSequence {
    public List my_sequence;
    
    public StructureSequence() {
        my_sequence = new ArrayList();
    }
    
    public void insertStructure(final Structure _structure) {
        my_sequence.add(_structure);
    }
}
