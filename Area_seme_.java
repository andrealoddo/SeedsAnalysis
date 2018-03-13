import ij.*;
import ij.plugin.filter.PlugInFilter;
import ij.plugin.filter.*;
import ij.process.*;
import ij.gui.*;
import ij.measure.*;
import ij.plugin.MeasurementsWriter;
import java.util.*;
import java.awt.*;

public class Perimeter_seme_ implements PlugInFilter {
    ImagePlus imp;
    protected ResultsTable rt = ResultsTable.getResultsTable();

    public int setup(String arg, ImagePlus imp) {
        this.imp = imp;
        return DOES_ALL;
    }

    public void run(ImageProcessor ip) {
        rt.reset();
        int x = 0, y = 0;
        int xe = ip.getWidth();
        int ye = ip.getHeight();
        int perimetro = 0;

        ip.findEdges();

        for (x = 0; x < xe; x++) {
            for (y = 0; y < ye; y++){
                if (ip.getPixel(x, y) == 255)
                    perimetro++;
            }
        }

        rt.incrementCounter();
        rt.addValue("Perimetro", perimetro);

        rt.addResults();
        rt.updateResults();
        rt.show("Risultati");
    }

}



