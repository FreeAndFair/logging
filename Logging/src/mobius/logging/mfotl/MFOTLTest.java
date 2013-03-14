package mobius.logging.mfotl;

public class MFOTLTest {
    /**
     * @param args
     * 
     * Test for formula parsing, evaluating and monitoring
     */
    public static void main(final String[] args) {
        final Signature test_signature = initializeSignature();  
        final TemporalStructure test_temporal_structure = initializeTemporalStructure();
        
        //final Monitor test_monitor = new Monitor("! E x ( in (x) & ! ( N[0,5) out(x) ))", test_signature);    
        final Monitor test_monitor = new Monitor("Ex ( in (x) ) & out (3)", test_signature);    
        test_monitor.runMonitor(test_temporal_structure); 
    }
    
    /**
     * Create a signature for the formula 
     * @param a_signature
     */
    private static Signature initializeSignature() {
        final /*@ non_null @*/ Signature a_signature = new Signature();
        a_signature.addPredicate(new Predicate("in", 1));
        a_signature.addPredicate(new Predicate("out", 1));
        return a_signature;
    }
    
    /**
     * Create a sequence of structures for testing
     * @param a_temporal_structure
     */
    private static TemporalStructure initializeTemporalStructure() {
        final /*@ non_null @*/ TemporalStructure a_temporal_structure = new TemporalStructure();
        Structure temp_structure = new Structure();
        int[] temp_value = {1};
        final String temp_rel1 = "in";
        final String temp_rel2 = "out";
        
        final Logger my_logger = new Logger(false);
        
        temp_structure.initRelationAssign(temp_rel1);
        temp_structure.addRelationAssign(temp_rel1, temp_value);
        temp_structure.initRelationAssign(temp_rel2);
        temp_value[0] = 3; // For testing
        temp_structure.addRelationAssign(temp_rel2, temp_value);
        my_logger.debug("-------------------------" + temp_structure.toString());
        a_temporal_structure.insertStructure(temp_structure, 1);
        
        temp_structure = new Structure();
        temp_structure.initRelationAssign(temp_rel1);
        temp_value[0] = 2;
        temp_structure.addRelationAssign(temp_rel1, temp_value);
        temp_structure.initRelationAssign(temp_rel2);
        my_logger.debug("-------------------------" + temp_structure.toString());
        a_temporal_structure.insertStructure(temp_structure, 1);
        
        temp_structure = new Structure();
        temp_structure.initRelationAssign(temp_rel1);
        temp_value[0] = 2;
        temp_structure.initRelationAssign(temp_rel2);
        temp_structure.addRelationAssign(temp_rel2, temp_value);
        my_logger.debug("-------------------------" + temp_structure.toString());
        a_temporal_structure.insertStructure(temp_structure, 3);
        
        
        temp_structure = new Structure();
        temp_structure.initRelationAssign(temp_rel1);
        temp_value[0] = 3;
        temp_structure.addRelationAssign(temp_rel1, temp_value);
        temp_structure.initRelationAssign(temp_rel2);
        temp_value[0] = 1;
        temp_structure.addRelationAssign(temp_rel2, temp_value);
        my_logger.debug("-------------------------" + temp_structure.toString());
        a_temporal_structure.insertStructure(temp_structure, 6);
        
        temp_structure = new Structure();
        temp_structure.initRelationAssign(temp_rel1);
        temp_structure.initRelationAssign(temp_rel2);
        my_logger.debug("-------------------------" + temp_structure.toString());
        a_temporal_structure.insertStructure(temp_structure, 7);
        
        temp_structure = new Structure();
        temp_structure.initRelationAssign(temp_rel1);
        temp_value[0] = 4;
        temp_structure.addRelationAssign(temp_rel1, temp_value);
        temp_structure.initRelationAssign(temp_rel2);
        my_logger.debug("-------------------------" + temp_structure.toString());
        a_temporal_structure.insertStructure(temp_structure, 9);
        
        temp_structure = new Structure();
        temp_structure.initRelationAssign(temp_rel1);
        temp_value[0] = 4;
        temp_structure.initRelationAssign(temp_rel2);
        temp_structure.addRelationAssign(temp_rel2, temp_value);
        my_logger.debug("-------------------------" + temp_structure.toString());
        a_temporal_structure.insertStructure(temp_structure, 13);
        
        return a_temporal_structure;
    }
}
