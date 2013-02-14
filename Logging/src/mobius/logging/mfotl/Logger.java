package mobius.logging.mfotl;

import java.io.PrintStream;

public class Logger {
    private final PrintStream logger_inst;
    
    public Logger() {
        logger_inst = getLogger();
    }
    
    private PrintStream getLogger() {
        return System.out;
    }
    
    public void debug(final String _debug) {
        logger_inst.println(_debug);
    }
    
    public void info(final String _info) {
        logger_inst.println(_info);
    }
    
    public void fatal(final String _fatal) {
        logger_inst.println(_fatal);
        System.exit(0);
    }
    
    public void error(final String _error) {
        logger_inst.println(_error);
        System.exit(1);
    }
}
