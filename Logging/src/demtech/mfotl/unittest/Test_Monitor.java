package demtech.mfotl.unittest;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import demtech.mfotl.Monitor;
import demtech.mfotl.Signature;
import demtech.mfotl.TemporalStructure;

@RunWith(value = Parameterized.class)
public class Test_Monitor {
    final private Monitor my_monitor_test;
    final private Monitor my_monitor_test0;
    final private Signature test_signature = TestSetting.initializeSignature("./src/demtech/mfotl/unittest/rv11.sig");
    final private Signature test_signature0 = TestSetting.initializeSignature("./src/demtech/mfotl/unittest/e1.sig");
    final private TemporalStructure test_ts = TestSetting.initializeTemporalStructure("./src/demtech/mfotl/unittest/rv11-1.log");
    final private TemporalStructure test_ts0 = TestSetting.initializeTemporalStructure("./src/demtech/mfotl/unittest/e1.log");
    
    public Test_Monitor(final String a_fs) {
        my_monitor_test0 = new Monitor(a_fs, test_signature0);
        my_monitor_test = new Monitor("True", test_signature);
    }
    
    @Parameters
    public static Collection<String[]> data() {
        //final String[][] data = new String[][] {{"True S approve(r)"}, {"publish(r) & (! (True S approve(r)))"}, {"!( E r (publish(r) & (! (True S approve(r)))))"}};
        /*final String[][] data = new String[][] {{"True"}, {"out (3)"}, {"P out (3)"}, 
                {"P (P ( out (3) ) )"}, {"E x ( out (x) & in(x) )"}, {"N out (4)"}, {"out (2) S [0,3) (in (2))"},
                {"(E x ( in (x) )) S [0,5) out (2)"}};*/
        final String[][] data = new String[][] {{"P out (3)"}};
        return Arrays.asList(data);
    }
    
    @Ignore
    public void test() {
        for (int i = 0; i < test_ts.getSize(); i++) {
            my_monitor_test.addStructure(test_ts.getStructure(i), test_ts.getTime(i));
        }
    }
    
    @Test
    public void test0() {
        for (int i = 0; i < test_ts0.getSize(); i++) {
            my_monitor_test0.addStructure(test_ts0.getStructure(i), test_ts0.getTime(i));
        }
    }
}
