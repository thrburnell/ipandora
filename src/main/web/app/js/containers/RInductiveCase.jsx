import { connect } from 'react-redux'
import InductiveCase from '../components/InductiveCase'

const mapStateToProps = (state) => (
  state.inductiveCase
)

const mapDispatchToProps = () => ({})

const RInductiveCase = connect(
  mapStateToProps,
  mapDispatchToProps
)(InductiveCase)

export default RInductiveCase

