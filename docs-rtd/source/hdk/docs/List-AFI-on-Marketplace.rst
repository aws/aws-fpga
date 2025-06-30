Listing Your AFI on AWS Marketplace
###################################

The AWS Marketplace enables you to sell your FPGA accelerator solutions to other AWS customers. You can list your AFI (Amazon FPGA Image) bundled with an AMI (Amazon Machine Image) that contains all necessary software components. AWS handles the metering, billing, and payment processing, allowing you to focus on your solution.

Prerequisites
-------------

Before listing your AFI on the AWS Marketplace:

1. Register as an AWS Marketplace seller at https://aws.amazon.com/marketplace/management/

2. Prepare your solution:

   * Create your AFI using the supported workflows in the `AWS FPGA Developer Kit <./../README.html#build-accelerator-afi-using-hdk-design-flow>`__
   * Build an `AMI <https://docs.aws.amazon.com/marketplace/latest/userguide/ami-products.html>`__ that includes all required software components:

     - Device drivers
     - Runtime engines
     - Libraries
     - Documentation

   * Test your complete solution thoroughly

3. Initiate AMI scanning via the `AMI Scanning page <https://docs.aws.amazon.com/marketplace/latest/userguide/product-and-ami-policies.html#security>`__.

Important Considerations
------------------------

* AFIs are always sold bundled with an AMI under a single product code
* AFIs are instance-type specific (e.g., an AFI created for F1 instances cannot be used with F2 instances)

Submission Process
------------------

1. Follow the `process <https://docs.aws.amazon.com/marketplace/latest/userguide/product-submission.html>`__ for submitting your product for publication

2. Review and Verification by AWS Marketplace team

   * Submission creates a case for the AWS Seller Operations team
   * AWS Support Engineer processes the product request and publish it to limited state
   * Upon completion of limited publishing, the AWS Support Engineer notifies the seller for verification and approval to go live
   * Seller conducts testing and validation

3. Final Publication

   * Seller provides formal AWS Marketplace approval
   * Seller Operations team proceeds with public release

For detailed information about AWS Marketplace policies and best practices, visit the `AWS Marketplace Seller Guide <https://docs.aws.amazon.com/marketplace/latest/userguide/what-is-marketplace.html>`__.
