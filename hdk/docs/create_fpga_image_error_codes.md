# AWS EC2 API create-fpga-image error codes

An AFI is created using an AWS API called `aws ec2 create-fpga-image`. When calling the API, the developer passes a pointer to an S3 bucket which contains a tar file.  The tar file includes the encrypted and compiled fpga image(a.k.a. Design Checkpoint or DCP) and a mandatory `manifest.txt` file. 

Example API Usage:
```
    $ aws ec2 create-fpga-image \
        --name <afi-name> \
        --description <afi-description> \
        --input-storage-location Bucket=<dcp-bucket-name>,Key=<path-to-tarball> \
        --logs-storage-location Bucket=<logs-bucket-name>,Key=<path-to-logs> \
	[ --client-token <value> ] \
	[ --dry-run | --no-dry-run ]
```

Errors can occurs when calling this API and this document provides the specification for the error codes.  

## Error Codes

* `INACCESSIBLE_INPUT` 
      *Error accessing resource in S3. Check permissions, naming, and ensure the bucket is within the same region as the API endpoint.*
      
* `INPUT_SIZE_ILLEGAL`
      *Input file size is not valid*
      
* `DCP_INTEGRITY_UNVERIFIED`
      *The DCP integrity SHA-256 hash does not match the provided DCP*
      
* `MANIFEST_NOT_FOUND`
      *No manifest file was found. See AWS FPGA HDK documentation for valid input format. We recommend using the scripts provided with AWS FPGA HDK*
      
* `MANIFEST_PARSE_FAILED`
      *Parsing the manifest file failed. We recommend using the scripts provided with AWS FPGA HDK*
      
* `SHELL_VERSION_INVALID`
      *The Shell Version provided is invalid*
      
* `SHELL_VERSION_DEPRECATED`
      *The Shell Version provided is deprecated*
      
* `PCIID_SYNTAX_INVALID`
      *PCI ID is not provided, wrongly formatted, or value is out of range valid range 1-65535 or 0x0001-0xFFFF*
      
* `PCIID_FORBIDDEN`
      *PCI ID value used is reserved. See AWS FPGA HDK documentation for reserved PCI*
      
* `CLK_ILLEGAL`
      *Provided clocks configuration is illegal. See AWS FPGA HDK documentation for supported clocks configuration*
      
* `CORRUPT_ARCHIVE`
      *Failed to parse the input tarball archive*
      
* `DCP_NOT_FOUND`
      *No DCP file was found with the supplied filename. See AWS FPGA HDK documentation for valid input format. We recommend using the scripts provided with AWS FPGA HDK*
      
* `DCP_CORRUPT`
      *Could not parse the input DCP. The DCP files seems to be corrupt*
 
* `DCP_NOT_ENCRYPTED`
      *The DCP was not encrypted*


