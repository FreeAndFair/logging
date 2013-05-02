package mobius.logging.mfotl;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;

public class MFOTLTest {
    /**
     * @param args
     * 
     * Test for formula parsing, evaluating and monitoring
     */
    public static void main(final String[] args) {
        final Signature test_signature = initializeSignature("./src/mobius/logging/mfotl/e1.sig");
        final TemporalStructure test_temporal_structure = initializeTemporalStructure("./src/mobius/logging/mfotl/e1.log");
        

        final Monitor test_monitor = new Monitor("in (2) U [0,5) out (2)", test_signature);
        
        //final Monitor test_monitor = new Monitor("E x ( in (x) ) S [0,5) out (2)", test_signature);
        //final Monitor test_monitor = new Monitor("E x ( in (x) ) S [0,5) out (2)", test_signature);
        //final Monitor test_monitor = new Monitor("out (2) S [0,3) (in (2))", test_signature);
        //final Monitor test_monitor = new Monitor("N (N out (4))", test_signature);
        //final Monitor test_monitor = new Monitor("E x (P[0,5) out (x))", test_signature);
        //final Monitor test_monitor = new Monitor("P (P out (3))", test_signature);
        //final Monitor test_monitor = new Monitor("P out (3)", test_signature);
        //final Monitor test_monitor = new Monitor("E x ( out (x) & in(x) )", test_signature);
        //final Monitor test_monitor = new Monitor("E x y ( out (x) & in(y) )", test_signature);
        //final Monitor test_monitor = new Monitor("E x y ( out (x) & in(3) )", test_signature);
        //final Monitor test_monitor = new Monitor("E x y ( out (x) )", test_signature);

        test_monitor.runMonitor(test_temporal_structure);
    }
    
    /**
     * Create a signature for the formula
     * @param a_signature
     */
    private static Signature initializeSignature(final String a_file) {
        final Signature a_signature = new Signature();
        
        try {
            FileInputStream fstream = new FileInputStream(a_file);
            DataInputStream in = new DataInputStream(fstream);
            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String str_line;
            while ((str_line = br.readLine()) != null) {
                System.out.println("Relation: " + str_line);
                String[] str_tokens = str_line.split(" ");
                int an_arity = str_tokens[1].split(",").length;
                a_signature.addPredicate(new Predicate(str_tokens[0], an_arity));
            }
            br.close();
            in.close();
            fstream.close();
        } catch (Exception e) {
            System.out.println("Current dir using System:" + System.getProperty("user.dir"));
            System.err.println("Error: " + e.getMessage());
        }

        return a_signature;
    }
    
    /**
     * Create a sequence of structures for testing
     * @param a_temporal_structure
     */
    private static TemporalStructure initializeTemporalStructure(final String a_file) {
        final TemporalStructure a_temporal_structure = new TemporalStructure();
        final Logger my_logger = new Logger(false);
        
        try {
            final FileInputStream fstream = new FileInputStream(a_file);
            final DataInputStream data_in = new DataInputStream(fstream);
            final BufferedReader buffer_reader = new BufferedReader(new InputStreamReader(data_in));
            String str_line, str_blk = buffer_reader.readLine() + "\n";
            
            if (!str_blk.contains("@")) {
                System.err.println("Log File is Not in Correct Format!!!");
                System.exit(1);
            }
            
            do {
                str_line = buffer_reader.readLine();
                if (str_line == null || str_line.contains("@")) {
                    String[] str_tokens = str_blk.split("\n");
                    int time = Integer.parseInt(str_tokens[0].substring(1));
                    Structure temp_structure = new Structure();                    
                    
                    for (int i = 1; i < str_tokens.length; i++) {
                        str_tokens[i] = str_tokens[i].substring(0, str_tokens[i].length()-1);
                        String[] str_tokens2 = str_tokens[i].split(" ");
                        String[] str_vals = str_tokens2[1].substring(1).split(",");
                        int[] int_vals = new int[str_vals.length];
                        for (int j = 0; j < int_vals.length; j++) {
                            int_vals[j] = Integer.parseInt(str_vals[j]);
                        }
                        
                        temp_structure.initRelationAssign(str_tokens2[0]);
                        temp_structure.addRelationAssign(str_tokens2[0], int_vals);
                    }

                    my_logger.debug("-------------------------" + temp_structure.toString());
                    a_temporal_structure.insertStructure(temp_structure, time);
                    str_blk = str_line+"\n";
                } else {
                    str_blk += (str_line + "\n");
                    continue;
                }
            } while (str_line != null);

            buffer_reader.close();
            data_in.close();
            fstream.close();
        } catch (Exception e) {
            //System.out.println("Current dir using System:" + System.getProperty("user.dir"));
            System.err.println("Error: " + e.getMessage());
        }
        
        return a_temporal_structure;
    }
}
