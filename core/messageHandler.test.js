// Import the message handler
import { createMessageHandler } from './messageHandler';

async function runTest() {
  console.log('Starting message handler test...');

  // Simulate creating a message handler. In a real scenario,
  // this would be part of the Prism runtime, providing a dispatch function.
  // We'll use a placeholder dispatch and an internal index.
  const dispatch = async (args) => {
    console.log('Dispatching:', args);
    // In a real scenario, dispatch would route messages to the correct handler.
    return 'Dispatch ACK';
  };

  const internalIndex = 1;
  const handler = await createMessageHandler(dispatch, internalIndex);

  // Define a sample message
  const message = { type: 'GREETING', payload: 'Hello, Prism!' };

  // Send the message to the handler
  try {
    const response = await handler.handleMessage(message);
    console.log('Test response:', response);
  } catch (error) {
    console.error('Test error:', error);
  }

  console.log('Message handler test finished.');
}

runTest();
