package mobius.logging.mfotl;

import java.util.ArrayList;
import java.util.List;

/*
 * 
 */
public class StructureSequence {
    public List sequence;
    
    public StructureSequence() {
        sequence = new ArrayList();
    }
    
    public void insertStructure(final Structure _structure) {
        sequence.add(_structure);
    }
}
