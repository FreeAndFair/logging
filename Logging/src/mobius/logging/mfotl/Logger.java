package mobius.logging.mfotl;

//TODO add specs and docs

import java.io.PrintStream;

public class Logger {
    private final PrintStream my_logger;
    
    public Logger() {
        my_logger = getLogger();
    }
    
    private PrintStream getLogger() {
        return System.out;
    }
    
    public void debug(final String _debug) {
        my_logger.println("debug: " + _debug);
    }
    
    public void debug(final String _debug[]) {
        my_logger.print("debug: ");
        for (int i = 0; i < _debug.length; i++) {
            my_logger.print(_debug[i]);
        }
        my_logger.println("");
    }
    
    public void info(final String _info) {
        my_logger.println("info: " + _info);
    }
    
    /*
     * fatal information, exit after output it
     */
    public void fatal(final String _fatal) {
        my_logger.println("fatal: " + _fatal);
        
        System.exit(0);
    }
    
    /*
     * error information, exit after output it
     */
    public void error(final String _error) {
        my_logger.println("error: " + _error);
        System.exit(1);
    }
}