import { reduxForm } from 'redux-form'
import AssertLine from '../../components/Proof/AssertLine'

export default reduxForm({
  form: "addProofLine",
  fields: ["formula"],
  onSubmit: () => console.log('Making proof step!')
})(AssertLine)

